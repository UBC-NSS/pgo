package distsys

import (
	. "github.com/onsi/ginkgo"
	. "github.com/onsi/gomega"

	"testing"
)

var _ = Describe("State Ownership", func() {
	var (
		stateHandler requestStateHandler
		store        DataStore
		group        *VarReq
		self         = "10.10.10.1"
	)

	BeforeEach(func() {
		store = NewDataStore(map[string]*DataEntry{
			"a": &DataEntry{Owner: "10.10.10.10"},
			"b": &DataEntry{Owner: "10.10.10.20"},
			"c": &DataEntry{Owner: "10.10.10.30"},
		})
	})

	var _ = Describe("localStateHandler", func() {
		BeforeEach(func() {
			// current state of the underlying global state store in the running node
			store.SetVal("a", 10)
			store.SetVal("b", 20)
			store.SetVal("c", 30)

			// which group of variables is being requested
			group = &VarReq{
				Peer: self,
				Names: []*BorrowSpecVariable{
					&BorrowSpecVariable{Name: "a", Exclusive: true},
					&BorrowSpecVariable{Name: "c", Exclusive: false},
				},
			}

			stateHandler = requestStateHandler{
				self:  self,
				group: group,
				store: store,

				migrationStrategy: NeverMigrate(self),
			}
		})

		var _ = Describe("GetState", func() {
			It("returns a series of values when all of the state is owned by that peer", func() {
				store.UpdateOwner("a", self)
				store.UpdateOwner("b", self)
				store.UpdateOwner("c", self)

				refs, _ := stateHandler.GetState()
				Expect(len(refs)).To(Equal(2))

				Expect(refs["a"]).To(Equal(&Reference{
					Type: REF_VAL,

					Peer:      self,
					Value:     10,
					Exclusive: true,
					Ownership: false,
				}))
				Expect(refs["c"]).To(Equal(&Reference{
					Type: REF_VAL,

					Peer:      self,
					Value:     30,
					Exclusive: false,
					Ownership: false,
				}))
			})

			It("returns a moved value when the running node no longer owns a variable", func() {
				// current node owns variable 'a', but not 'c'
				store.UpdateOwner("a", self)

				refs, _ := stateHandler.GetState()
				Expect(len(refs)).To(Equal(2))

				Expect(refs["a"]).To(Equal(&Reference{
					Type:      REF_VAL,
					Peer:      self,
					Value:     10,
					Exclusive: true,
					Ownership: false,
				}))
				Expect(refs["c"]).To(Equal(&Reference{
					Type: REF_MOVED,
					Peer: "10.10.10.30",
				}))
			})

			It("skips values that it owns if previous variables moved", func() {
				// request for variables 'a', 'b' and 'c'
				group.Names = append(group.Names, group.Names[1])
				group.Names[1] = &BorrowSpecVariable{Name: "b", Exclusive: true}

				// running node owns 'a' and 'c', but not 'b'
				store.UpdateOwner("a", self)
				store.UpdateOwner("c", self)

				refs, _ := stateHandler.GetState()
				Expect(len(refs)).To(Equal(3))

				Expect(refs["a"]).To(Equal(&Reference{
					Type:      REF_VAL,
					Peer:      self,
					Value:     10,
					Exclusive: true,
					Ownership: false,
				}))

				Expect(refs["b"]).To(Equal(&Reference{
					Type: REF_MOVED,
					Peer: "10.10.10.20",
				}))

				Expect(refs["c"]).To(Equal(&Reference{
					Type: REF_SKIP,
				}))
			})

			It("indicates all variables that have moved", func() {
				// request for variables 'a', 'b' and 'c'
				group.Names = append(group.Names, group.Names[1])
				group.Names[1] = &BorrowSpecVariable{Name: "b", Exclusive: true}

				// running node owns 'a', but not 'b' and 'c'
				store.UpdateOwner("a", self)

				refs, _ := stateHandler.GetState()
				Expect(len(refs)).To(Equal(3))

				Expect(refs["a"]).To(Equal(&Reference{
					Type:      REF_VAL,
					Peer:      self,
					Value:     10,
					Exclusive: true,
					Ownership: false,
				}))

				Expect(refs["b"]).To(Equal(&Reference{
					Type: REF_MOVED,
					Peer: "10.10.10.20",
				}))

				Expect(refs["c"]).To(Equal(&Reference{
					Type: REF_MOVED,
					Peer: "10.10.10.30",
				}))
			})
		})
	})
})

func TestStateOwnership(t *testing.T) {
	RegisterFailHandler(Fail)
	RunSpecs(t, "StateOwnership")
}
