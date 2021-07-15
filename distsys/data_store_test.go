package distsys

import (
	. "github.com/onsi/ginkgo"
	. "github.com/onsi/gomega"

	"testing"
)

var _ = Describe("DataStore", func() {
	var (
		store DataStore
	)

	BeforeEach(func() {
		store = NewDataStore(map[string]*DataEntry{
			"a": &DataEntry{Value: 10, Owner: "10.10.10.10"},
			"b": &DataEntry{Value: 20, Owner: "10.10.10.20"},
			"c": &DataEntry{Value: 30, Owner: "10.10.10.30"},
		})
	})

	var _ = Describe("Lock", func() {
		It("panics if the name given is not known", func() {
			unknownName := func() {
				store.Lock("unknown")
			}

			Expect(unknownName).To(Panic())
		})

		It("locks the entry with the name given", func() {
			// name exists -- does not panic
			store.Lock("a")

			// locks successfully -- now able to unlock
			store.Unlock("a")
		})
	})

	var _ = Describe("Unlock", func() {
		It("panics if the name given is not known", func() {
			unknownName := func() {
				store.Unlock("unknown")
			}

			Expect(unknownName).To(Panic())
		})
	})

	var _ = Describe("GetVal", func() {
		It("panics if the name given is not known", func() {
			unknownName := func() {
				store.GetVal("unknown")
			}

			Expect(unknownName).To(Panic())
		})

		It("returns the value associated with an existing name", func() {
			Expect(store.GetVal("a")).To(Equal(10))
			Expect(store.GetVal("b")).To(Equal(20))
			Expect(store.GetVal("c")).To(Equal(30))
		})
	})

	var _ = Describe("SetVal", func() {
		It("panics if the name given is not known", func() {
			unknownName := func() {
				store.SetVal("unknown", 40)
			}

			Expect(unknownName).To(Panic())
		})

		It("updates the value associated with an existing name", func() {
			store.SetVal("a", 40)

			Expect(store.GetVal("a")).To(Equal(40))
			Expect(store.GetVal("b")).To(Equal(20))
			Expect(store.GetVal("c")).To(Equal(30))
		})
	})

	var _ = Describe("OwnerOf", func() {
		It("panics if the name given is not known", func() {
			unknownName := func() {
				store.OwnerOf("unknown")
			}

			Expect(unknownName).To(Panic())
		})

		It("returns the address of the owner of an existing name", func() {
			Expect(store.OwnerOf("a")).To(Equal("10.10.10.10"))
			Expect(store.OwnerOf("b")).To(Equal("10.10.10.20"))
			Expect(store.OwnerOf("c")).To(Equal("10.10.10.30"))
		})
	})

	var _ = Describe("UpdateOwner", func() {
		It("panics if the name given is not known", func() {
			unknownName := func() {
				store.UpdateOwner("unknown", "10.10.10.40")
			}

			Expect(unknownName).To(Panic())
		})

		It("updates the address of the owner of an existing name", func() {
			store.UpdateOwner("a", "10.10.10.40")

			Expect(store.OwnerOf("a")).To(Equal("10.10.10.40"))
			Expect(store.OwnerOf("b")).To(Equal("10.10.10.20"))
			Expect(store.OwnerOf("c")).To(Equal("10.10.10.30"))
		})
	})
})

func TestDataStore(t *testing.T) {
	RegisterFailHandler(Fail)
	RunSpecs(t, "DataStore")
}
