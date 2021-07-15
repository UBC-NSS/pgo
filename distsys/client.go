package distsys

// stateHandler defines the interface of a state handler. Apart from the definitions
// of localStateHandler, which manipulate state located within the running node's
// local store, there is also the possibility that state lives in another node
// in the system, and a similar interface is required
type stateHandler interface {
	GetState() (VarReferences, error)
	ReleaseState(VarReferences) error
}

// remoteHandler implements stateHandler for the case where state lives in a different
// node in the network
type remoteHandler struct {
	group       *VarReq
	stateServer *StateServer
}

// GetState retrieves state that lives in another node in the system. The ownership table
// needs to be locked before this function is called since the variable may have
// moved.
func (remote remoteHandler) GetState() (VarReferences, error) {
	conn := remote.stateServer.connections.GetConnection(remote.group.Peer)
	remote.group.Requester = remote.stateServer.self
	refs := VarReferences(map[string]*Reference{})

	// unlock local references before we request remote state
	for _, borrowVar := range remote.group.Names {
		remote.stateServer.store.Unlock(borrowVar.Name)
	}

	if err := conn.Call("StateServer.GetState", remote.group, &refs); err != nil {
		return nil, err
	}

	return refs, nil
}

// ReleaseState releases state that lives in another system. This function needs to be
// called once a counterpart GetState call has succeeded.
func (remote remoteHandler) ReleaseState(refs VarReferences) error {
	var ok bool
	conn := remote.stateServer.connections.GetConnection(remote.group.Peer)

	// include only references for variables included in the group
	// being released
	releaseNames := []string{}
	for _, borrowVar := range remote.group.Names {
		releaseNames = append(releaseNames, borrowVar.Name)
	}

	refSlice := VarReferences(map[string]*Reference{})
	for name, ref := range refs {
		for _, releaseName := range releaseNames {
			if releaseName == name {
				refSlice[name] = ref
				break
			}
		}
	}

	if err := conn.Call("StateServer.ReleaseState", &refSlice, &ok); err != nil {
		return err
	}

	return nil
}

// stateBuilder returns a stateHandler that either manipulates state in the running node's
// local store, or sends messages to the node that currently owns the state contained
// in the VarReq struct.
func stateBuilder(group *VarReq, ss *StateServer) stateHandler {
	if group.Peer == ss.self {
		return localStateHandler{
			group: group,
			store: ss.store,
			self:  ss.self,
		}
	}

	return remoteHandler{group, ss}
}

// Acquire receives a BorrowSpec and returns a populated VarReferences struct containing
// the values of the variables in the spec given, with the requested permissions (i.e.,
// exclusive or non-exclusive (read-only) access).
func (ss *StateServer) Acquire(spec *BorrowSpec) (VarReferences, error) {
	op := NewGlobalStateOperation(spec, ss.store, ss.self, ss.connections)
	allRefs := VarReferences(map[string]*Reference{})

	// lock every variable that is being requested to avoid migrations
	// while we determine request groups
	op.Lock()

	for op.HasNext() {
		group := op.Next()
		op.UnlockExcept(group)

		refs, err := stateBuilder(group, ss).GetState()
		if err != nil {
			return nil, err
		}

		holds := op.UpdateRefs(refs)
		op.AckMigrations()
		allRefs = allRefs.Merge(holds)

		op.Lock()
	}

	return allRefs, nil
}

// Release receives a set of references to variables, potentially manipulated by
// the application (after a call to Acquire), and releases any locks that were
// held, either locally or remotely on a different node in the system.
func (ss *StateServer) Release(refs VarReferences) error {
	op := NewGlobalStateOperation(refs.ToBorrowSpec(), ss.store, ss.self, ss.connections)

	for _, group := range op.Groups() {
		if err := stateBuilder(group, ss).ReleaseState(refs); err != nil {
			return err
		}
	}

	// unlock local entries after releasing our locks remotely
	op.Unlock()

	return nil
}

// func (net *Network) Close() error {
// 	net.connections.Close()
// 	return nil
// }
