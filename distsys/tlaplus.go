package distsys

import (
	"bytes"
	"encoding/binary"
	"encoding/gob"
	"errors"
	"fmt"
	"github.com/benbjohnson/immutable"
	"hash/fnv"
	"io"
	"math"
	"strconv"
	"strings"
)

var TLATypeError = errors.New("TLA+ type error")

func init() {
	gob.Register(tlaValueBool(false))
	gob.Register(tlaValueNumber(0))
	gob.Register(tlaValueString(""))
	gob.Register(&tlaValueSet{})
	gob.Register(&tlaValueTuple{})
}

type TLAValue struct {
	data tlaValueImpl
}

var _ fmt.Stringer = TLAValue{}

func (v TLAValue) Hash() uint32 {
	if v.data == nil {
		return 0
	} else {
		return v.data.Hash()
	}
}

func (v TLAValue) Equal(other TLAValue) bool {
	if v.data == nil && other.data == nil {
		return true
	} else if v.data == nil || other.data == nil {
		return false
	} else {
		return v.data.Equal(other)
	}
}

func (v TLAValue) String() string {
	if v.data == nil {
		return "defaultInitValue"
	} else {
		return v.data.String()
	}
}

func (v *TLAValue) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	return decoder.Decode(&v.data)
}

func (v *TLAValue) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	err := encoder.Encode(&v.data)
	return buf.Bytes(), err
}

func require(req bool, msg string) {
	if !req {
		panic(fmt.Errorf("%w: %s", TLATypeError, msg))
	}
}

func (v TLAValue) AsBool() bool {
	switch data := v.data.(type) {
	case tlaValueBool:
		return bool(data)
	default:
		panic(fmt.Errorf("%w: %v is not a boolean", TLATypeError, v))
	}
}

func (v TLAValue) AsNumber() int32 {
	switch data := v.data.(type) {
	case tlaValueNumber:
		return int32(data)
	default:
		panic(fmt.Errorf("%w: %v is not a number", TLATypeError, v))
	}
}

func (v TLAValue) AsString() string {
	switch data := v.data.(type) {
	case tlaValueString:
		return string(data)
	default:
		panic(fmt.Errorf("%w: %v is not a string", TLATypeError, v))
	}
}

func (v TLAValue) AsSet() *immutable.Map {
	switch data := v.data.(type) {
	case *tlaValueSet:
		return data.Map
	default:
		panic(fmt.Errorf("%w: %v is not a set", TLATypeError, v))
	}
}

func (v TLAValue) AsTuple() *immutable.List {
	switch data := v.data.(type) {
	case *tlaValueTuple:
		return data.List
	default:
		panic(fmt.Errorf("%w: %v is not a tuple", TLATypeError, v))
	}
}

func (v TLAValue) AsFunction() *immutable.Map {
	switch data := v.data.(type) {
	case *tlaValueFunction:
		return data.Map
	default:
		panic(fmt.Errorf("%w: %v is not a function", TLATypeError, v))
	}
}

func (v TLAValue) SelectElement() TLAValue {
	set := v.AsSet()
	it := set.Iterator()
	if !it.Done() {
		key, _ := it.Next()
		return key.(TLAValue)
	} else {
		panic(fmt.Errorf("%w: tried to select an element of %v, which was an empty set", TLATypeError, v))
	}
}

func (v TLAValue) ApplyFunction(argument TLAValue) TLAValue {
	switch data := v.data.(type) {
	case *tlaValueTuple:
		return data.Get(int(argument.AsNumber())).(TLAValue)
	case *tlaValueFunction:
		value, ok := data.Get(argument)
		if !ok {
			panic(fmt.Errorf("%w: function %v's domain does not contain index %v", TLATypeError, v, argument))
		}
		return value.(TLAValue)
	default:
		panic(fmt.Errorf("%w: could not apply %v", TLATypeError, v))
	}
}

func (v TLAValue) PCalPrint() {
	fmt.Println(v)
}

func TLA_EqualsSymbol(lhs, rhs TLAValue) TLAValue {
	return NewTLABool(lhs.Equal(rhs))
}

func TLA_NotEqualsSymbol(lhs, rhs TLAValue) TLAValue {
	return NewTLABool(!lhs.Equal(rhs))
}

type TLAValueHasher struct{}

var _ immutable.Hasher = TLAValueHasher{}

func (TLAValueHasher) Hash(key interface{}) uint32 {
	return key.(TLAValue).Hash()
}

func (TLAValueHasher) Equal(a, b interface{}) bool {
	return a.(TLAValue).Equal(b.(TLAValue))
}

type tlaValueImpl interface {
	Hash() uint32
	Equal(other TLAValue) bool
	String() string
}

type tlaValueBool bool

var _ tlaValueImpl = tlaValueBool(false)

var TLA_TRUE = TLAValue{tlaValueBool(true)}
var TLA_FALSE = TLAValue{tlaValueBool(false)}
var TLA_BOOLEAN = NewTLASet(TLA_TRUE, TLA_FALSE)

func NewTLABool(v bool) TLAValue {
	if v {
		return TLA_TRUE
	} else {
		return TLA_FALSE
	}
}

func (v tlaValueBool) Hash() uint32 {
	h := fnv.New32()
	err := binary.Write(h, binary.LittleEndian, bool(v))
	if err != nil {
		panic(err)
	}
	return h.Sum32()
}

func (v tlaValueBool) Equal(other TLAValue) bool {
	return bool(v) == other.AsBool()
}

func (v tlaValueBool) String() string {
	if v {
		return "TRUE"
	} else {
		return "FALSE"
	}
}

func TLA_LogicalAndSymbol(lhs, rhs TLAValue) TLAValue {
	return NewTLABool(lhs.AsBool() && rhs.AsBool())
}

func TLA_LogicalOrSymbol(lhs, rhs TLAValue) TLAValue {
	return NewTLABool(lhs.AsBool() || rhs.AsBool())
}

func TLA_LogicalNotSymbol(v TLAValue) TLAValue {
	return NewTLABool(!v.AsBool())
}

func TLA_ImpliesSymbol(lhs, rhs TLAValue) TLAValue {
	return NewTLABool(!lhs.AsBool() || rhs.AsBool())
}

func TLA_EquivSymbol(lhs, rhs TLAValue) TLAValue {
	return NewTLABool(lhs.AsBool() == rhs.AsBool())
}

type tlaValueNumber int32

var _ tlaValueImpl = tlaValueNumber(0)

func NewTLANumber(num int32) TLAValue {
	return TLAValue{tlaValueNumber(num)}
}

// FIXME: better error handling
var TLA_Nat = TLAValue{}
var TLA_Int = TLAValue{}

func (v tlaValueNumber) Hash() uint32 {
	h := fnv.New32()
	err := binary.Write(h, binary.LittleEndian, int32(v))
	if err != nil {
		panic(err)
	}
	return h.Sum32()
}

func (v tlaValueNumber) Equal(other TLAValue) bool {
	return int32(v) == other.AsNumber()
}

func (v tlaValueNumber) String() string {
	return strconv.FormatInt(int64(v), 10)
}

func TLA_PlusSymbol(lhs, rhs TLAValue) TLAValue {
	return NewTLANumber(lhs.AsNumber() + rhs.AsNumber())
}

func TLA_MinusSymbol(lhs, rhs TLAValue) TLAValue {
	return NewTLANumber(lhs.AsNumber() - rhs.AsNumber())
}

func TLA_AsteriskSymbol(lhs, rhs TLAValue) TLAValue {
	return NewTLANumber(lhs.AsNumber() * rhs.AsNumber())
}

func TLA_SuperscriptSymbol(lhs, rhs TLAValue) TLAValue {
	return NewTLANumber(int32(math.Pow(float64(lhs.AsNumber()), float64(rhs.AsNumber()))))
}

func TLA_LessThanOrEqualSymbol(lhs, rhs TLAValue) TLAValue {
	return NewTLABool(lhs.AsNumber() <= rhs.AsNumber())
}

func TLA_GreaterThanOrEqualSymbol(lhs, rhs TLAValue) TLAValue {
	return NewTLABool(lhs.AsNumber() >= rhs.AsNumber())
}

func TLA_LessThanSymbol(lhs, rhs TLAValue) TLAValue {
	return NewTLABool(lhs.AsNumber() < rhs.AsNumber())
}

func TLA_GreaterThanSymbol(lhs, rhs TLAValue) TLAValue {
	return NewTLABool(lhs.AsNumber() > rhs.AsNumber())
}

func TLA_DotDotSymbol(lhs, rhs TLAValue) TLAValue {
	from, to := lhs.AsNumber(), rhs.AsNumber()
	builder := immutable.NewListBuilder()
	for i := from; i <= to; i++ {
		builder.Append(i)
	}
	return TLAValue{&tlaValueTuple{builder.List()}}
}

func TLA_DivSymbol(lhs, rhs TLAValue) TLAValue {
	rhsNum := rhs.AsNumber()
	require(rhsNum != 0, "divisor must not be 0")
	return NewTLANumber(lhs.AsNumber() / rhsNum)
}

func TLA_PercentSymbol(lhs, rhs TLAValue) TLAValue {
	rhsNum := rhs.AsNumber()
	require(rhsNum != 0, "divisor must not be 0")
	return NewTLANumber(lhs.AsNumber() % rhsNum)
}

func TLA_NegationSymbol(v TLAValue) TLAValue {
	return NewTLANumber(-v.AsNumber())
}

type tlaValueString string

var _ tlaValueImpl = tlaValueString("")

func NewTLAString(value string) TLAValue {
	return TLAValue{tlaValueString(value)}
}

func (v tlaValueString) Hash() uint32 {
	vC := string(v)
	h := fnv.New32()
	_, err := h.Write([]byte(vC))
	if err != nil {
		panic(err)
	}
	return h.Sum32()
}

func (v tlaValueString) Equal(other TLAValue) bool {
	return string(v) == other.AsString()
}

func (v tlaValueString) String() string {
	return strconv.Quote(string(v))
}

type tlaValueSet struct {
	*immutable.Map
}

var _ tlaValueImpl = new(tlaValueSet)

func NewTLASet(members ...TLAValue) TLAValue {
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	for _, member := range members {
		builder.Set(member, true)
	}
	return TLAValue{&tlaValueSet{builder.Map()}}
}

func (v *tlaValueSet) Hash() uint32 {
	var hash uint32 = 0
	it := v.Iterator()
	for !it.Done() {
		key, _ := it.Next()
		keyV := key.(TLAValue)
		// use XOR combination, so that all the set members are hashed out of order
		hash ^= keyV.Hash()
	}
	h := fnv.New32()
	err := binary.Write(h, binary.LittleEndian, hash)
	if err != nil {
		panic(err)
	}
	return h.Sum32()
}

func (v *tlaValueSet) Equal(other TLAValue) bool {
	oC := other.AsSet()
	if v.Len() != oC.Len() {
		return false
	} else {
		it := v.Iterator()
		for !it.Done() {
			k, _ := it.Next()
			_, ok := oC.Get(k)
			if !ok {
				return false
			}
		}
		it = oC.Iterator()
		for !it.Done() {
			k, _ := it.Next()
			_, ok := v.Get(k)
			if !ok {
				return false
			}
		}
		return true
	}
}

func (v *tlaValueSet) String() string {
	builder := strings.Builder{}
	builder.WriteString("{")
	it := v.Iterator()
	first := true
	for !it.Done() {
		if first {
			first = false
		} else {
			builder.WriteString(", ")
		}
		elem, _ := it.Next()
		builder.WriteString(elem.(TLAValue).String())
	}
	builder.WriteString("}")
	return builder.String()
}

func (v *tlaValueSet) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	it := v.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		err := encoder.Encode(elem.(TLAValue))
		if err != nil {
			return nil, err
		}
	}
	return buf.Bytes(), nil
}

func (v *tlaValueSet) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	for {
		var elem TLAValue
		err := decoder.Decode(&elem)
		if err != nil {
			if errors.Is(err, io.EOF) {
				v.Map = builder.Map()
				return nil
			} else {
				return err
			}
		}
		builder.Set(elem, true)
	}
}

func TLAQuantifiedUniversal(setVals []TLAValue, pred func([]TLAValue) bool) TLAValue {
	var sets []*immutable.Map
	for _, val := range setVals {
		sets = append(sets, val.AsSet())
	}

	predArgs := make([]TLAValue, len(sets))

	var helper func(idx int) bool
	helper = func(idx int) bool {
		if idx == len(sets) {
			return pred(predArgs)
		}

		it := sets[idx].Iterator()
		for !it.Done() {
			elem, _ := it.Next()
			predArgs[idx] = elem.(TLAValue)
			if !helper(idx + 1) {
				return false
			}
		}
		return true
	}

	return NewTLABool(helper(0))
}

func TLAQuantifiedExistential(setVals []TLAValue, pred func([]TLAValue) bool) TLAValue {
	var sets []*immutable.Map
	for _, val := range setVals {
		sets = append(sets, val.AsSet())
	}

	predArgs := make([]TLAValue, len(sets))

	var helper func(idx int) bool
	helper = func(idx int) bool {
		if idx == len(sets) {
			return pred(predArgs)
		}

		it := sets[idx].Iterator()
		for !it.Done() {
			elem, _ := it.Next()
			predArgs[idx] = elem.(TLAValue)
			if helper(idx + 1) {
				return true
			}
		}
		return false
	}

	return NewTLABool(helper(0))
}

func TLASetRefinement(setVal TLAValue, pred func(TLAValue) bool) TLAValue {
	set := setVal.AsSet()
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	it := set.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		if pred(elem.(TLAValue)) {
			builder.Set(elem, true)
		}
	}
	return TLAValue{&tlaValueSet{builder.Map()}}
}

func TLASetComprehension(setVals []TLAValue, body func([]TLAValue) TLAValue) TLAValue {
	var sets []*immutable.Map
	for _, val := range setVals {
		sets = append(sets, val.AsSet())
	}

	builder := immutable.NewMapBuilder(TLAValueHasher{})
	bodyArgs := make([]TLAValue, len(sets))

	var helper func(idx int)
	helper = func(idx int) {
		if idx == len(sets) {
			builder.Set(body(bodyArgs), true)
		} else {
			it := sets[idx].Iterator()
			for !it.Done() {
				elem, _ := it.Next()
				bodyArgs[idx] = elem.(TLAValue)
				helper(idx + 1)
			}
		}
	}

	helper(0)
	return TLAValue{&tlaValueSet{builder.Map()}}
}

func TLA_InSymbol(lhs, rhs TLAValue) TLAValue {
	set := rhs.AsSet()
	_, ok := set.Get(lhs)
	return NewTLABool(ok)
}

func TLA_NotInSymbol(lhs, rhs TLAValue) TLAValue {
	set := rhs.AsSet()
	_, ok := set.Get(lhs)
	return NewTLABool(!ok)
}

func TLA_IntersectSymbol(lhs, rhs TLAValue) TLAValue {
	lhsSet, rhsSet := lhs.AsSet(), rhs.AsSet()
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	it := lhsSet.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		if _, ok := rhsSet.Get(elem); ok {
			builder.Set(elem, true)
		}
	}
	return TLAValue{&tlaValueSet{builder.Map()}}
}

func TLA_UnionSymbol(lhs, rhs TLAValue) TLAValue {
	lhsSet, rhsSet := lhs.AsSet(), rhs.AsSet()
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	it := lhsSet.Iterator()
	for !it.Done() {
		v, _ := it.Next()
		builder.Set(v, true)
	}
	it = rhsSet.Iterator()
	for !it.Done() {
		v, _ := it.Next()
		builder.Set(v, true)
	}
	return TLAValue{&tlaValueSet{builder.Map()}}
}

func TLA_SubsetOrEqualSymbol(lhs, rhs TLAValue) TLAValue {
	lhsSet, rhsSet := lhs.AsSet(), rhs.AsSet()
	it := lhsSet.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		_, ok := rhsSet.Get(elem)
		if !ok {
			return TLA_FALSE
		}
	}
	return TLA_TRUE
}

func TLA_BackslashSymbol(lhs, rhs TLAValue) TLAValue {
	lhsSet, rhsSet := lhs.AsSet(), rhs.AsSet()
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	it := lhsSet.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		if _, ok := rhsSet.Get(elem); !ok {
			builder.Set(elem, true)
		}
	}
	return TLAValue{&tlaValueSet{builder.Map()}}
}

func TLA_PrefixSubsetSymbol(v TLAValue) TLAValue {
	set := v.AsSet()
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	shrinkingSet := set
	it := set.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		builder.Set(shrinkingSet, true)
		shrinkingSet = shrinkingSet.Delete(elem)
	}
	builder.Set(shrinkingSet, true) // add the empty set
	return TLAValue{&tlaValueSet{builder.Map()}}
}

func TLA_PrefixUnionSymbol(v TLAValue) TLAValue {
	setOfSets := v.AsSet()
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	it := setOfSets.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		set := elem.(TLAValue).AsSet()
		innerIt := set.Iterator()
		for !innerIt.Done() {
			elem, _ := it.Next()
			builder.Set(elem, true)
		}
	}
	return TLAValue{&tlaValueSet{builder.Map()}}
}

func TLA_IsFiniteSet(v TLAValue) TLAValue {
	_ = v.AsSet() // it should at least _be_ a set, even if we're sure it's finite
	return TLA_TRUE
}

func TLA_Cardinality(v TLAValue) TLAValue {
	return NewTLANumber(int32(v.AsSet().Len()))
}

type tlaValueTuple struct {
	*immutable.List
}

var _ tlaValueImpl = new(tlaValueTuple)

func NewTLATuple(members ...TLAValue) TLAValue {
	builder := immutable.NewListBuilder()
	for _, member := range members {
		builder.Append(member)
	}
	return TLAValue{&tlaValueTuple{builder.List()}}
}

func (v *tlaValueTuple) Hash() uint32 {
	h := fnv.New32()
	it := v.Iterator()
	for !it.Done() {
		_, member := it.Next()
		memberV := member.(TLAValue)
		err := binary.Write(h, binary.LittleEndian, memberV.Hash())
		if err != nil {
			panic(err)
		}
	}
	return h.Sum32()
}

func (v *tlaValueTuple) Equal(other TLAValue) bool {
	otherTuple := other.AsTuple()
	if v.Len() != otherTuple.Len() {
		return false
	}
	it1, it2 := v.Iterator(), otherTuple.Iterator()
	for !it1.Done() || !it2.Done() {
		_, elem1 := it1.Next()
		_, elem2 := it2.Next()
		if !elem1.(TLAValue).data.Equal(elem2.(TLAValue)) {
			return false
		}
	}
	return true
}

func (v *tlaValueTuple) String() string {
	builder := strings.Builder{}
	builder.WriteString("<<")
	it := v.Iterator()
	first := true
	for !it.Done() {
		if first {
			first = false
		} else {
			builder.WriteString(", ")
		}
		_, elem := it.Next()
		builder.WriteString(elem.(TLAValue).String())
	}
	builder.WriteString(">>")
	return builder.String()
}

func (v *tlaValueTuple) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	it := v.Iterator()
	for !it.Done() {
		_, elem := it.Next()
		err := encoder.Encode(elem)
		if err != nil {
			return nil, err
		}
	}
	return buf.Bytes(), nil
}

func (v *tlaValueTuple) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	builder := immutable.NewListBuilder()
	for {
		var elem TLAValue
		err := decoder.Decode(&elem)
		if err != nil {
			if errors.Is(err, io.EOF) {
				v.List = builder.List()
				return nil
			} else {
				return err
			}
		}
		builder.Append(elem)
	}
}

func TLA_Seq(v TLAValue) TLAValue {
	set := v.AsSet()
	// move all the elements onto a slice for easier handling
	var elems []TLAValue
	it := set.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		elems = append(elems, elem.(TLAValue))
	}

	// prepare to build a set of tuples
	builder := immutable.NewMapBuilder(TLAValueHasher{})

	// special-case the empty set, as the main process doesn't handle it
	if len(elems) == 0 {
		builder.Set(NewTLATuple(), true)
	} else {
		// generate permutations using Heap's algorithm
		var generatePermutations func(k int)
		generatePermutations = func(k int) {
			if k == 1 {
				// store a new tuple in the set
				builder.Set(NewTLATuple(elems...), true)
			} else {
				generatePermutations(k - 1)

				for i := 0; i < k-1; i += 1 {
					if k%2 == 0 {
						elems[i], elems[k-1] = elems[k-1], elems[i]
					} else {
						elems[0], elems[k-1] = elems[k-1], elems[0]
					}
					generatePermutations(k - 1)
				}
			}
		}

		generatePermutations(len(elems))
	}

	return TLAValue{&tlaValueSet{builder.Map()}}
}

func TLA_Len(v TLAValue) TLAValue {
	return NewTLANumber(int32(v.AsTuple().Len()))
}

func TLA_OSymbol(lhs, rhs TLAValue) TLAValue {
	lhsTuple, rhsTuple := lhs.AsTuple(), rhs.AsTuple()
	it := rhsTuple.Iterator()
	for !it.Done() {
		_, elem := it.Next()
		lhsTuple = lhsTuple.Append(elem)
	}
	return TLAValue{&tlaValueTuple{lhsTuple}}
}

func TLA_Append(lhs, rhs TLAValue) TLAValue {
	return TLAValue{&tlaValueTuple{lhs.AsTuple().Append(rhs)}}
}

func TLA_Head(v TLAValue) TLAValue {
	tuple := v.AsTuple()
	require(tuple.Len() > 0, "to call Head, tuple must not be empty")
	return tuple.Get(0).(TLAValue)
}

func TLA_Tail(v TLAValue) TLAValue {
	tuple := v.AsTuple()
	require(tuple.Len() > 0, "to call Tail, tuple must not be empty")
	return TLAValue{&tlaValueTuple{tuple.Slice(1, tuple.Len())}}
}

func TLA_SubSeq(v, m, n TLAValue) TLAValue {
	tuple := v.AsTuple()
	from, to := int(m.AsNumber()), int(n.AsNumber())
	require(from <= to && from >= 0 && to <= tuple.Len(), "to call SubSeq, from and to indices must be in-bounds")
	return TLAValue{&tlaValueTuple{tuple.Slice(from-1, to)}}
}

// TODO: TLA_SelectSeq, uses predicate
func TLA_SelectSeq(a, b TLAValue) TLAValue {
	panic("implement me")
}

type tlaValueFunction struct {
	*immutable.Map
}

type TLARecordField struct {
	Key, Value TLAValue
}

func (field TLARecordField) Hash() uint32 {
	h := fnv.New32()
	err := binary.Write(h, binary.LittleEndian, field.Key.Hash())
	if err != nil {
		panic(err)
	}
	err = binary.Write(h, binary.LittleEndian, field.Value.Hash())
	if err != nil {
		panic(err)
	}
	return h.Sum32()
}

var _ tlaValueImpl = &tlaValueFunction{}

func NewTLAFunction(setVals []TLAValue, body func([]TLAValue) TLAValue) TLAValue {
	require(len(setVals) > 0, "the domain of a TLA+ function cannot be the product of no sets")
	builder := immutable.NewMapBuilder(TLAValueHasher{})

	var sets []*immutable.Map
	for _, val := range setVals {
		sets = append(sets, val.AsSet())
	}

	bodyArgs := make([]TLAValue, len(sets))

	var helper func(idx int)
	helper = func(idx int) {
		if idx == len(bodyArgs) {
			builder.Set(NewTLATuple(bodyArgs...), body(bodyArgs))
		} else {
			it := sets[idx].Iterator()
			for !it.Done() {
				elem, _ := it.Next()
				bodyArgs[idx] = elem.(TLAValue)
				helper(idx + 1)
			}
		}
	}
	helper(0)

	return TLAValue{&tlaValueFunction{builder.Map()}}
}

func NewTLARecord(pairs []TLARecordField) TLAValue {
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	for _, pair := range pairs {
		builder.Set(pair.Key, pair.Value)
	}
	return TLAValue{&tlaValueFunction{builder.Map()}}
}

func NewTLARecordSet(pairs []TLARecordField) TLAValue {
	recordSet := immutable.NewMap(TLAValueHasher{})
	// start with a set of one empty map
	recordSet = recordSet.Set(TLAValue{&tlaValueFunction{immutable.NewMap(TLAValueHasher{})}}, true)
	for _, pair := range pairs {
		fieldValueSet := pair.Value.AsSet()
		builder := immutable.NewMapBuilder(TLAValueHasher{})
		// iterate over accumulated set of records, and add every possible value for this field, from fieldValueSet
		it := recordSet.Iterator()
		for !it.Done() {
			acc, _ := it.Next()
			accFn := acc.(TLAValue).AsFunction()
			valIt := fieldValueSet.Iterator()
			for !valIt.Done() {
				val, _ := valIt.Next()
				builder.Set(TLAValue{&tlaValueFunction{accFn.Set(pair.Key, val)}}, true)
			}
		}
		recordSet = builder.Map()
	}
	return TLAValue{&tlaValueSet{recordSet}}
}

func NewTLAFunctionSet(from, to TLAValue) TLAValue {
	fromSet, _ := from.AsSet(), to.AsSet()
	var pairs []TLARecordField
	it := fromSet.Iterator()
	for !it.Done() {
		key, _ := it.Next()
		pairs = append(pairs, TLARecordField{
			Key:   key.(TLAValue),
			Value: to,
		})
	}
	return NewTLARecordSet(pairs)
}

func (v *tlaValueFunction) Hash() uint32 {
	var hash uint32
	it := v.Iterator()
	for !it.Done() {
		key, value := it.Next()
		hash ^= TLARecordField{Key: key.(TLAValue), Value: value.(TLAValue)}.Hash()
	}
	h := fnv.New32()
	err := binary.Write(h, binary.LittleEndian, hash)
	if err != nil {
		panic(err)
	}
	return h.Sum32()
}

func (v *tlaValueFunction) Equal(other TLAValue) bool {
	otherFunction := other.AsFunction()
	if v.Len() != otherFunction.Len() {
		return false
	}
	it := v.Iterator()
	for !it.Done() {
		key, value := it.Next()
		otherValue, ok := otherFunction.Get(key)
		if !ok || !value.(TLAValue).Equal(otherValue.(TLAValue)) {
			return false
		}
	}
	return true
}

func (v *tlaValueFunction) String() string {
	builder := strings.Builder{}
	builder.WriteString("(")
	first := true
	it := v.Iterator()
	for !it.Done() {
		key, value := it.Next()
		if first {
			first = false
		} else {
			builder.WriteString(" @@ ")
		}
		builder.WriteString("(")
		builder.WriteString(key.(TLAValue).String())
		builder.WriteString(") :> (")
		builder.WriteString(value.(TLAValue).String())
		builder.WriteString(")")
	}
	builder.WriteString(")")
	return builder.String()
}

func (v *tlaValueFunction) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	it := v.Iterator()
	for !it.Done() {
		key, value := it.Next()
		err := encoder.Encode(TLARecordField{
			Key:   key.(TLAValue),
			Value: value.(TLAValue),
		})
		if err != nil {
			return nil, err
		}
	}
	return buf.Bytes(), nil
}

func (v *tlaValueFunction) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	for {
		var field TLARecordField
		err := decoder.Decode(&field)
		if err != nil {
			if errors.Is(err, io.EOF) {
				v.Map = builder.Map()
				return nil
			} else {
				return err
			}
		}
		builder.Set(field.Key, field.Value)
	}
}

type TLAFunctionSubstitutionRecord struct {
	Keys  []TLAValue
	Value func(anchor TLAValue) TLAValue
}

func TLAFunctionSubstitution(source TLAValue, substitutions []TLAFunctionSubstitutionRecord) TLAValue {
	var keysHelper func(source TLAValue, keys []TLAValue, value func(anchor TLAValue) TLAValue) TLAValue
	keysHelper = func(source TLAValue, keys []TLAValue, value func(anchor TLAValue) TLAValue) TLAValue {
		if len(keys) == 0 {
			return value(source)
		} else {
			sourceFn := source.AsFunction()
			val, keyOk := sourceFn.Get(keys[0])
			require(keyOk, "invalid key during function substitution")
			sourceFn = sourceFn.Set(keys[0], keysHelper(val.(TLAValue), keys[1:], value))
			return TLAValue{&tlaValueFunction{sourceFn}}
		}
	}
	for _, substitution := range substitutions {
		source = keysHelper(source, substitution.Keys, substitution.Value)
	}
	return source
}

func TLA_DomainSymbol(v TLAValue) TLAValue {
	fn := v.AsFunction()
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	it := fn.Iterator()
	for !it.Done() {
		domainElem, _ := it.Next()
		builder.Set(domainElem, true)
	}
	return TLAValue{&tlaValueSet{builder.Map()}}
}
