package distsys

import (
	. "github.com/onsi/ginkgo"
	. "github.com/onsi/gomega"

	"testing"
)

var _ = Describe("Distsys package", func() {
	var (
		store DataStore
		self  = "10.10.10.1"
	)

	BeforeEach(func() {
		store = NewDataStore(map[string]*DataEntry{
			"a": &DataEntry{Owner: "10.10.10.10"},
			"b": &DataEntry{Owner: "10.10.10.20"},
			"c": &DataEntry{Owner: "10.10.10.30"},
		})
	})

	var _ = Describe("BorrowSpec", func() {
		Context("Sorting entries", func() {
			It("Sorts an empty spec", func() {
				spec := BorrowSpec{
					ReadNames:  []string{},
					WriteNames: []string{},
				}

				sorted := spec.Sorted()
				Expect(len(sorted)).To(Equal(0))
			})

			It("Sorts disjoint read and write names", func() {
				spec := BorrowSpec{
					ReadNames:  []string{"a", "c"},
					WriteNames: []string{"d", "b"},
				}

				sorted := spec.Sorted()
				Expect(len(sorted)).To(Equal(4))

				Expect(sorted[0].Name).To(Equal("a"))
				Expect(sorted[0].Exclusive).To(Equal(false))

				Expect(sorted[1].Name).To(Equal("b"))
				Expect(sorted[1].Exclusive).To(Equal(true))

				Expect(sorted[2].Name).To(Equal("c"))
				Expect(sorted[2].Exclusive).To(Equal(false))

				Expect(sorted[3].Name).To(Equal("d"))
				Expect(sorted[3].Exclusive).To(Equal(true))
			})

			It("Sorts read and write names with non-empty intersections", func() {
				spec := BorrowSpec{
					ReadNames:  []string{"b", "a"},
					WriteNames: []string{"c", "b"},
				}

				sorted := spec.Sorted()
				Expect(len(sorted)).To(Equal(3))

				Expect(sorted[0].Name).To(Equal("a"))
				Expect(sorted[0].Exclusive).To(Equal(false))

				Expect(sorted[1].Name).To(Equal("b"))
				Expect(sorted[1].Exclusive).To(Equal(true))

				Expect(sorted[2].Name).To(Equal("c"))
				Expect(sorted[2].Exclusive).To(Equal(true))
			})
		})
	})

	var _ = Describe("GlobalStateOperation", func() {
		Context("Grouping variables", func() {
			It("panics if Next() is called on an empty spec", func() {
				op := NewGlobalStateOperation(&BorrowSpec{}, store, self, nil)

				getNext := func() {
					op.Next()
				}

				Expect(op.HasNext()).To(Equal(false))
				Expect(getNext).To(Panic())
			})

			It("Groups a spec where no grouping is possible", func() {
				spec := &BorrowSpec{ReadNames: []string{"a", "b", "c"}, WriteNames: []string{"b"}}
				op := NewGlobalStateOperation(spec, store, self, nil)

				groups := op.Groups()
				Expect(len(groups)).To(Equal(3))

				Expect(groups[0].Peer).To(Equal("10.10.10.10"))
				Expect(len(groups[0].Names)).To(Equal(1))
				Expect(groups[0].Names[0].Name).To(Equal("a"))
				Expect(groups[0].Names[0].Exclusive).To(Equal(false))

				Expect(groups[1].Peer).To(Equal("10.10.10.20"))
				Expect(len(groups[1].Names)).To(Equal(1))
				Expect(groups[1].Names[0].Name).To(Equal("b"))
				Expect(groups[1].Names[0].Exclusive).To(Equal(true))

				Expect(groups[2].Peer).To(Equal("10.10.10.30"))
				Expect(len(groups[2].Names)).To(Equal(1))
				Expect(groups[2].Names[0].Name).To(Equal("c"))
				Expect(groups[2].Names[0].Exclusive).To(Equal(false))
			})

			It("Groups a spec where some grouping of variables is possible", func() {
				spec := &BorrowSpec{ReadNames: []string{"a", "b", "c"}, WriteNames: []string{"b"}}
				op := NewGlobalStateOperation(spec, store, self, nil)

				// co-locate variables 'a' and 'b'
				store.UpdateOwner("b", store.OwnerOf("a"))

				groups := op.Groups()
				Expect(len(groups)).To(Equal(2))

				// group 1: 'a' (non-exclusive) and 'b' (exclusive)
				Expect(groups[0].Peer).To(Equal("10.10.10.10"))
				Expect(len(groups[0].Names)).To(Equal(2))
				Expect(groups[0].Names[0].Name).To(Equal("a"))
				Expect(groups[0].Names[0].Exclusive).To(Equal(false))
				Expect(groups[0].Names[1].Name).To(Equal("b"))
				Expect(groups[0].Names[1].Exclusive).To(Equal(true))

				// group 2: 'c' (non-exclusive)
				Expect(groups[1].Peer).To(Equal("10.10.10.30"))
				Expect(len(groups[1].Names)).To(Equal(1))
				Expect(groups[1].Names[0].Name).To(Equal("c"))
				Expect(groups[1].Names[0].Exclusive).To(Equal(false))
			})

			It("Groups a spec where every variable is owned by the same peer", func() {
				spec := &BorrowSpec{ReadNames: []string{"a", "b", "c"}, WriteNames: []string{"b"}}
				op := NewGlobalStateOperation(spec, store, self, nil)

				// co-locate variables 'a', 'b' and 'c'
				store.UpdateOwner("b", store.OwnerOf("a"))
				store.UpdateOwner("c", store.OwnerOf("a"))

				groups := op.Groups()
				Expect(len(groups)).To(Equal(1))

				Expect(groups[0].Peer).To(Equal("10.10.10.10"))
				Expect(len(groups[0].Names)).To(Equal(3))

				Expect(groups[0].Names[0].Name).To(Equal("a"))
				Expect(groups[0].Names[0].Exclusive).To(Equal(false))

				Expect(groups[0].Names[1].Name).To(Equal("b"))
				Expect(groups[0].Names[1].Exclusive).To(Equal(true))

				Expect(groups[0].Names[2].Name).To(Equal("c"))
				Expect(groups[0].Names[2].Exclusive).To(Equal(false))
			})
		})

		var _ = Describe("UpdateRefs", func() {
			It("Detects no more variables are left if all references are present", func() {
				spec := &BorrowSpec{ReadNames: []string{"a", "b", "c"}, WriteNames: []string{"b"}}
				op := NewGlobalStateOperation(spec, store, self, nil)

				refs := VarReferences(map[string]*Reference{
					"a": &Reference{Type: REF_VAL, Value: 10},
					"b": &Reference{Type: REF_VAL, Value: 20},
					"c": &Reference{Type: REF_VAL, Value: 30},
				})

				holds := op.UpdateRefs(refs)
				Expect(holds).To(Equal(refs))

				Expect(op.HasNext()).To(Equal(false))
			})

			It("Updates the ownership table when a moved references are received", func() {
				spec := &BorrowSpec{ReadNames: []string{"a", "b", "c"}, WriteNames: []string{"b"}}
				op := NewGlobalStateOperation(spec, store, self, nil)

				refs := VarReferences(map[string]*Reference{
					"a": &Reference{Type: REF_VAL, Value: 10},
					"b": &Reference{Type: REF_MOVED, Peer: "10.10.10.10"},
					"c": &Reference{Type: REF_MOVED, Peer: "10.10.10.10"},
				})

				holds := op.UpdateRefs(refs)
				Expect(len(holds)).To(Equal(1))

				Expect(holds).To(Equal(VarReferences(map[string]*Reference{
					"a": &Reference{Type: REF_VAL, Value: 10},
				})))

				Expect(op.HasNext()).To(Equal(true))
				Expect(op.Next()).To(Equal(&VarReq{
					Peer: "10.10.10.10",
					Names: []*BorrowSpecVariable{
						&BorrowSpecVariable{Name: "b", Exclusive: true},
						&BorrowSpecVariable{Name: "c", Exclusive: false},
					},
				}))
			})

			It("updates the ownership table and local store when ownership is received", func() {
				spec := &BorrowSpec{ReadNames: []string{"a", "b", "c"}, WriteNames: []string{"b"}}
				op := NewGlobalStateOperation(spec, store, self, nil)

				refs := VarReferences(map[string]*Reference{
					"a": &Reference{Type: REF_VAL, Value: 10, Ownership: true, Peer: "10.10.10.40"},
					"b": &Reference{Type: REF_MOVED, Peer: "10.10.10.10"},
					"c": &Reference{Type: REF_SKIP},
				})

				holds := op.UpdateRefs(refs)
				Expect(len(holds)).To(Equal(1))

				Expect(holds).To(Equal(VarReferences(map[string]*Reference{
					"a": &Reference{Type: REF_VAL, Value: 10, Ownership: true, Peer: "10.10.10.40"},
				})))

				Expect(op.HasNext()).To(Equal(true))
				Expect(op.Next()).To(Equal(&VarReq{
					Peer: "10.10.10.10",
					Names: []*BorrowSpecVariable{
						&BorrowSpecVariable{Name: "b", Exclusive: true},
					},
				}))

				// updates the ownership table to indicate that the current node
				// now owns variable 'a'
				Expect(store.OwnerOf("a")).To(Equal(self))

				// updates the local store with the value received
				Expect(store.GetVal("a")).To(Equal(10))

				// has a list of variables to acknowledge ownership about
				Expect(op.ownerships).To(Equal([]string{"a"}))
			})
		})
	})

	var _ = Describe("VarReferences", func() {
		It("updates its contents", func() {
			refs := VarReferences(map[string]*Reference{
				"a": &Reference{Value: "old", Exclusive: true},
			})

			refs.Set("a", "new")

			Expect(refs).To(Equal(VarReferences(map[string]*Reference{
				"a": &Reference{Value: "new", Exclusive: true},
			})))
		})

		It("gets the correct content", func() {
			refs := VarReferences(map[string]*Reference{
				"a": &Reference{Value: "old", Exclusive: true},
			})

			s := refs.Get("a").(string)

			Expect(refs).To(Equal(VarReferences(map[string]*Reference{
				"a": &Reference{Value: "old", Exclusive: true},
			})))

			Expect(s).To(Equal("old"))
		})

		var _ = Describe("Merge", func() {
			var target VarReferences

			BeforeEach(func() {
				target = VarReferences(map[string]*Reference{
					"a": &Reference{Value: "refs1:a", Exclusive: true},
					"b": &Reference{Value: "refs1:b", Exclusive: false},
				})
			})

			It("Merges with an empty VarReferences", func() {
				other := VarReferences(map[string]*Reference{})

				Expect(target.Merge(other)).To(Equal(target))
			})

			It("is able to merge with another VarReferences", func() {
				other := VarReferences(map[string]*Reference{
					"b": &Reference{Value: "refs2:b", Exclusive: true},
				})

				Expect(target.Merge(other)).To(Equal(VarReferences(map[string]*Reference{
					"a": &Reference{Value: "refs1:a", Exclusive: true},
					"b": &Reference{Value: "refs2:b", Exclusive: true},
				})))
			})
		})

		It("is able to generate a corresponding BorrowSpec", func() {
			refs := VarReferences(map[string]*Reference{
				"c": &Reference{Value: []int{1, 2, 3}, Exclusive: true},
				"a": &Reference{Value: 10, Exclusive: false},
				"b": &Reference{Value: "PGo", Exclusive: true},
			})

			spec := refs.ToBorrowSpec()

			Expect(len(spec.ReadNames)).To(Equal(1))
			Expect(spec.ReadNames[0]).To(Equal("a"))

			Expect(len(spec.WriteNames)).To(Equal(2))
			Expect(spec.WriteNames[0]).To(Equal("b"))
			Expect(spec.WriteNames[1]).To(Equal("c"))
		})
	})

})

func TestDistsys(t *testing.T) {
	RegisterFailHandler(Fail)
	RunSpecs(t, "Distsys")
}
