package distsys

/////////////////////////////////////////////////////////////////////////////////////
// Details on distributed global state and how the underlying protocol works can  //
// be found at https://github.com/UBC-NSS/pgo/wiki/Distributed-Global-State      //
//////////////////////////////////////////////////////////////////////////////////

// GetState is an RPC call used by nodes in the system to request parts
// of the global state that are believed to be owned by the running node.
// Not all variables contained in the VarReq struct passed as argument
// to this function could be owned by this function (the caller may have
// out of date ownership information), in which case this function will
// include references pointing to the actual owner of the state.
func (iface *StateServerRPC) GetState(req *VarReq, refs *VarReferences) error {
	handler := requestStateHandler{
		group:     req,
		requester: req.Requester,
		store:     iface.server.store,
		self:      iface.server.self,

		migrationStrategy: iface.server.migrationStrategy,
	}

	state, err := handler.GetState()
	if err != nil {
		return err
	}

	*refs = state
	return nil
}

// ReleaseState is an RPC call used by nodes in the system in order to release
// state previously held with a counterpart GetState() call. The references passed
// to this function *must* be owned by the current node.
func (iface *StateServerRPC) ReleaseState(refs VarReferences, ok *bool) error {
	handler := requestStateHandler{store: iface.server.store, self: iface.server.self}

	if err := handler.ReleaseState(refs); err != nil {
		return err
	}

	*ok = true
	return nil
}

// OwnershipMoved is an RPC call used by nodes to indicate that a previous
// move of ownership of a piece of state is acknowledged by the receiving
// end. The local entry for the variables that were moved can, therefore,
// be unlocked.
func (iface *StateServerRPC) OwnershipMoved(req *VarReq, ok *bool) error {
	handler := requestStateHandler{store: iface.server.store, group: req}
	handler.StateMoveComplete()

	*ok = true
	return nil
}
