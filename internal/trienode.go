package internal

import (
	"fmt"
	"math"
)

type TrieKey struct {
	// Some thought was put into alignment and struct size here but there isn't
	// much that can be done. Since the `Bits` slice has a required alignment
	// of 8 and size 24, and `Length` is the only other field in the struct, it
	// has 8 bytes to stretch out in no matter what size integer is used.
	Length uint
	Bits   []byte
}

type TrieNode struct {
	TrieKey
	Data interface{}
	// Some thought was put into alignment here. The following three fields fit
	// within an 8-byte required alignment on x86_64 at least
	size     uint32
	h        uint16
	isActive bool
	children [2]*TrieNode
}

// bitsToBytes calculates the number of bytes (including possible
// least-significant partial) to hold the given number of bits.
func bitsToBytes(bits uint) uint {
	return (bits + 7) / 8
}

// numCommonBits calculates the number of consecutive common most-significant
// bits between two bytes: a and b. The following table shows how the equation
// was derived.
//
// This function assumes that a != b. It will get the wrong answer otherwise! A
// more general form of this function should check if a == b and return 8.
//
// |  x = a^b | log2(x) | floor | 7 - floor | result
// |----------|---------|-------|-----------|-------
// [  0,   1) | [-∞, 0) | NA    | NA        | not possible since a != b
// [  1,   2) | [ 0, 1) | 0     | 7         | 7 bits in common
// [  2,   4) | [ 1, 2) | 1     | 6         | 6 bits in common
// [  4,   8) | [ 2, 3) | 2     | 5         | 5 bits in common
// [  8,  16) | [ 3, 4) | 3     | 4         | 4 bits in common
// [ 16,  32) | [ 4, 5) | 4     | 3         | 3 bits in common
// [ 32,  64) | [ 5, 6) | 5     | 2         | 2 bits in common
// [ 64, 128) | [ 6, 7) | 6     | 1         | 1 bits in common
// [128, 256) | [ 7, 8) | 7     | 0         | 0 bits in common
func numCommonBits(a, b byte) uint {
	return 7 - uint(math.Log2(float64(a^b)))
}

// contains is a helper which compares to see if the shorter prefix contains the
// longer.
//
// This function is not generally safe. It assumes non-nil pointers, that
// smaller.Length < larger.Length, and that the `Bits` slices are at least
// large enough to hold `Length` bits for each TrieKey.
//
// `prematchedBits`: This argument is for internal use only.
//                   It is an optimization to avoid comparing bytes that have
//                   already been matched higher up in the tree.
//
// `matches`: is true if the shorter key is a prefix of the longer key.
// `exact`: is true if the two keys are exactly the same (implies `matches`)
// `common`: is always the number of bits that the two keys have in common
// `child`: tells whether the first non-common bit in `longer` is a 0 or 1. It
//          is only valid if either `matches` or `exact` is false. The
//          following table describes how to interpret results.

// | matches | exact | child | note
// |---------|-------|-------|-------
// | false   | NA    | 0     | the two are disjoint and `longer` compares less than `shorter`
// | false   | NA    | 1     | the two are disjoint and `longer` compares greater than `shorter`
// | true    | false | 0     | `longer` belongs in `shorter`'s `children[0]`
// | true    | false | 1     | `longer` belongs in `shorter`'s `children[1]`
// | true    | true  | NA    | `shorter` and `longer` are the same key
func contains(shorter, longer *TrieKey, prematchedBits uint) (matches, exact bool, common, child uint) {
	// Two variables important in finding which child to descend into
	var pivotByte, numBytes uint
	pivotMask := byte(0x80)

	// calculate `exact`, `common`, and `child` at the end with defer
	defer func() {
		if !matches {
			var s, l byte

			// We know both of these slices are large enough to index with
			// `numBytes` because `matches` is false and therefore it must have
			// been a previous comparison of these bytes that got us here.
			for i := prematchedBits / 8; i <= numBytes; i++ {
				s, l = shorter.Bits[i], longer.Bits[i]
				if s == l {
					continue
				}

				common = 8*i + numCommonBits(s, l)

				// Whether `longer` goes on the left (0) or right (1)
				if longer.Bits[i] < shorter.Bits[i] {
					child = 0
				} else {
					child = 1
				}
				return
			}
		}

		common = shorter.Length
		exact = shorter.Length == longer.Length
		if !exact {
			// Whether `longer` goes on the left (0) or right (1)
			if longer.Bits[pivotByte]&pivotMask == 0 {
				child = 0
			} else {
				child = 1
			}
		}
	}()

	// Prefix length of 0 matches everything!
	if shorter.Length == 0 {
		matches = true
		return
	}

	// The bits to compare in the two keys always follows the following pattern:
	// 1. any number of leading "full" bytes which must match exactly
	// 2. 0 or 1 "partial" byte in the least significant (last) position which
	//    must match up to the number of partial bits (1-7 bits).
	//
	// The strategy here is to compare the bytes from the least significant
	// (last) to the most significant (first) to avoid redundantly comparing
	// bytes that might have already matched higher in the tree.

	// Calculate number of bytes (including possible least-significant partial)
	// Decrement this as we compare bytes up to the most significant.
	numBytes = bitsToBytes(shorter.Length)

	// Figure out how many bits are in the partial byte (0 means no partial)
	maskLen := shorter.Length % 8

	// If the last byte is partial, compare using a bitmask
	if maskLen > 0 {
		var mask byte
		mask = 0xff << (8 - maskLen)

		// decrement before comparing since the slices are indexed from 0
		numBytes--
		if shorter.Bits[numBytes]&mask != longer.Bits[numBytes]&mask {
			matches = false
			return
		}

		pivotMask >>= maskLen
	}

	pivotByte = numBytes

	// The other bytes are all full and can be compared simply
	for numBytes > (prematchedBits / 8) {
		// decrement before comparing since the slices are indexed from 0
		numBytes--
		if shorter.Bits[numBytes] != longer.Bits[numBytes] {
			matches = false
			return
		}
	}

	matches = true
	return
}

// compare is a helper which compares two keys to find their relationship
//
// This function is not generally safe. It assumes non-nil pointers and that
// the `Bits` slices are at least large enough to hold `Length` bits for each
// TrieKey.
func compare(a, b *TrieKey, prematchedBits uint) (a_match, b_match, reversed bool, common, child uint) {
	// Figure out which is the longer prefix and reverse them if b is shorter
	reversed = b.Length < a.Length
	if reversed {
		b_match, a_match, common, child = contains(b, a, prematchedBits)
	} else {
		a_match, b_match, common, child = contains(a, b, prematchedBits)
	}
	return
}

// Get is the public form of get(...)
func (me *TrieNode) GetOrInsert(searchKey *TrieKey, data interface{}) (newHead, result *TrieNode, err error) {
	if searchKey == nil {
		return nil, nil, fmt.Errorf("cannot insert nil key")
	}

	newHead, result = me.getOrInsert(searchKey, data, 0)
	return
}

func (me *TrieNode) setSize() {
	// me is not nil by design
	me.size = uint32(me.children[0].Size() + me.children[1].Size())
	me.h = 1 + uint16(uint16(intMax(me.children[0].height(), me.children[1].height())))
	if me.isActive {
		me.size++
	}
}

// getOrInsert returns the existing value if an exact match is found, otherwise, inserts the given default
func (me *TrieNode) getOrInsert(searchKey *TrieKey, data interface{}, prematchedBits uint) (head, result *TrieNode) {
	defer func() {
		if result == nil {
			result = &TrieNode{TrieKey: *searchKey, Data: data}

			// The only error from insert is that the key already exists. But, that cannot happen by design.
			head, _ = me.insert(result, true, false, prematchedBits)
		}
	}()

	if me == nil || searchKey.Length < me.TrieKey.Length {
		return
	}

	matches, exact, _, child := contains(&me.TrieKey, searchKey, prematchedBits)
	if !matches {
		return
	}

	if !exact {
		head = me
		var newChild *TrieNode
		newChild, result = me.children[child].getOrInsert(searchKey, data, me.TrieKey.Length)
		me.children[child] = newChild
		me.setSize()
		return
	}

	if !me.isActive {
		return
	}

	return me, me
}

// Match is the public form of match(...)
func (me *TrieNode) Match(searchKey *TrieKey) *TrieNode {
	if searchKey == nil {
		return nil
	}

	return me.match(searchKey, 0)
}

// match returns the existing entry with the longest prefix that fully contains
// the prefix given by the key argument or nil if none match.
//
// "contains" means that the first "Length" bits in the entry's key are exactly
// the same as the same number of first bits in the given search key. This
// implies the search key is at least as long as any matching node's prefix.
//
// Some examples include the following ipv4 and ipv6 matches:
//     10.0.0.0/24 contains 10.0.0.0/24, 10.0.0.0/25, and 10.0.0.0/32
//     2001:cafe:beef::/64 contains 2001:cafe:beef::a/124
//
// "longest" means that if multiple existing entries in the trie match the one
// with the longest length will be returned. It is the most specific match.
func (me *TrieNode) match(searchKey *TrieKey, prematchedBits uint) *TrieNode {
	if me == nil {
		return nil
	}

	nodeKey := &me.TrieKey
	if searchKey.Length < nodeKey.Length {
		return nil
	}

	matches, exact, _, child := contains(nodeKey, searchKey, prematchedBits)
	if !matches {
		return nil
	}

	if !exact {
		if better := me.children[child].match(searchKey, me.TrieKey.Length); better != nil {
			return better
		}
	}

	if !me.isActive {
		return nil
	}

	return me
}

// Size returns the number of entries in the trie
func (me *TrieNode) Size() int {
	if me == nil {
		return 0
	}
	return int(me.size)
}

// height returns the maximum height of the trie.
func (me *TrieNode) height() int {
	if me == nil {
		return 0
	}
	return int(me.h)
}

func intMax(a, b int) int {
	if a < b {
		return b
	}
	return a
}

// Update updates the key / value only if the key already exists
func (me *TrieNode) Update(key *TrieKey, data interface{}) (newHead *TrieNode, err error) {
	if key == nil {
		return nil, fmt.Errorf("cannot insert nil key")
	}
	return me.insert(&TrieNode{TrieKey: *key, Data: data}, false, true, 0)
}

// InsertOrUpdate inserts the key / value if the key didn't previously exist.
// Otherwise, it updates the data.
func (me *TrieNode) InsertOrUpdate(key *TrieKey, data interface{}) (newHead *TrieNode, err error) {
	if key == nil {
		return nil, fmt.Errorf("cannot insert nil key")
	}
	return me.insert(&TrieNode{TrieKey: *key, Data: data}, true, true, 0)
}

// Insert is the public form of insert(...)
func (me *TrieNode) Insert(key *TrieKey, data interface{}) (newHead *TrieNode, err error) {
	if key == nil {
		return nil, fmt.Errorf("cannot insert nil key")
	}
	return me.insert(&TrieNode{TrieKey: *key, Data: data}, true, false, 0)
}

// insert adds a node into the trie and return the new root of the trie. It is
// important to note that the root of the trie can change. If the new node
// cannot be inserted, nil is returned.
func (me *TrieNode) insert(node *TrieNode, insert, update bool, prematchedBits uint) (newHead *TrieNode, err error) {
	defer func() {
		if err == nil && newHead != nil {
			node.size = 1
			node.h = 1
			node.isActive = true
			newHead.setSize()
		}
	}()

	if me == nil {
		if !insert {
			return me, fmt.Errorf("the key doesn't exist to update")
		}
		return node, nil
	}

	// Test containership both ways
	trie_contains, node_contains, reversed, common, child := compare(&me.TrieKey, &node.TrieKey, prematchedBits)
	switch {
	case trie_contains && node_contains:
		// They have the same key
		if me.isActive && !update {
			return me, fmt.Errorf("a node with that key already exists")
		}
		if !me.isActive && !insert {
			return me, fmt.Errorf("the key doesn't exist to update")
		}
		node.children = me.children
		return node, nil

	case trie_contains && !node_contains:
		// Trie node's key contains the new node's key. Insert it.
		newChild, err := me.children[child].insert(node, insert, update, me.Length)
		if err == nil {
			me.children[child] = newChild
		}
		return me, err

	case !trie_contains && node_contains:
		if !insert {
			return me, fmt.Errorf("the key doesn't exist to update")
		}
		// New node's key contains the trie node's key. Insert new node as the parent of the trie.
		node.children[child] = me
		return node, nil

	default:
		if !insert {
			return me, fmt.Errorf("the key doesn't exist to update")
		}
		// Keys are disjoint. Create a new (inactive) parent node to join them side-by-side.
		var children [2]*TrieNode

		if (child == 1) != reversed { // (child == 1) XOR reversed
			children[0], children[1] = me, node
		} else {
			children[0], children[1] = node, me
		}

		numBytes := bitsToBytes(common)
		bits := make([]byte, numBytes)
		copy(bits, me.Bits)

		// zero out the bits that are not in common in the last byte
		numBits := common % 8
		if numBits != 0 {
			bits[numBytes-1] &= ^(byte(0xff) >> numBits)
		}

		return &TrieNode{
			TrieKey: TrieKey{
				Bits:   bits,
				Length: common,
			},
			children: children,
		}, nil
	}
}

// Delete is a public form of del(...) below
func (me *TrieNode) Delete(key *TrieKey) (newHead *TrieNode, err error) {
	return me.del(key, 0)
}

// del removes a node into the trie given a key and returns the new root of
// the trie. It is important to note that the root of the trie can change.
func (me *TrieNode) del(key *TrieKey, prematchedBits uint) (newHead *TrieNode, err error) {
	defer func() {
		if err == nil && newHead != nil {
			newHead.size = uint32(newHead.children[0].Size() + newHead.children[1].Size())
			newHead.h = 1 + uint16(uint16(intMax(newHead.children[0].height(), newHead.children[1].height())))
			if newHead.isActive {
				newHead.size++
			}
		}
	}()

	if me == nil {
		return me, fmt.Errorf("cannot delete from a nil")
	}

	if key == nil {
		return me, fmt.Errorf("cannot delete nil key")
	}

	trie_contains, node_contains, _, _, child := compare(&me.TrieKey, key, prematchedBits)
	if !trie_contains {
		return me, fmt.Errorf("key not found")
	}

	if !node_contains {
		// Trie node's key contains the key. Delete recursively.
		newChild, err := me.children[child].del(key, me.TrieKey.Length)
		if err == nil {
			me.children[child] = newChild
		}
		return me, err
	}

	// The key matches this node exactly, delete this node
	me.isActive = false

	if me.children[0] != nil {
		if me.children[1] != nil {
			// The two children are disjoint so keep this inactive node.
			return me, nil
		}

		return me.children[0], nil
	}

	// At this point, it doesn't matter if it is nil or not
	return me.children[1], nil
}

// active returns whether a node represents an active prefix in the tree (true)
// or an intermediate node (false). It is safe to call on a nil pointer.
func (me *TrieNode) active() bool {
	if me == nil {
		return false
	}
	return me.isActive
}

type dataContainer struct {
	valid bool
	data  interface{}
}

// EqualComparable is an interface used to compare data. If the datatype you
// store implements it, it can be used to aggregate prefixes.
type EqualComparable interface {
	EqualInterface(interface{}) bool
}

func dataEqual(a, b dataContainer) bool {
	if !(a.valid && b.valid) {
		return false
	}
	// If the data stored are EqualComparable, compare it using its method.
	// This is useful to allow mapping to a more complex type (e.g.
	// netaddr.IPSet)  that is not comparable by normal means.
	switch t := a.data.(type) {
	case EqualComparable:
		return t.EqualInterface(b.data)
	default:
		return a.data == b.data
	}
}

// aggregable returns if descendants can be aggregated into the current prefix,
// it considers the `isActive` attributes of all nodes under consideration and
// only aggregates where active nodes can be joined together in aggregation. It
// also only aggregates nodes whose data compares equal.
//
// returns true and the data used to compare with if they are aggregable, false
// otherwise (and data must be ignored).
func (me *TrieNode) aggregable(data dataContainer) (bool, dataContainer) {
	// Note that me != nil by design

	if me.isActive {
		return true, dataContainer{valid: true, data: me.Data}
	}

	// Thoughts on aggregation.
	//
	// If a parent node's data compares equal to that of descendent nodes, then
	// the descendent nodes should not be included in the aggregation. If there
	// is an intermediate descendent between two nodes that doesn't compare
	// equal, then all of them should be included. Another way to put this is
	// that each time a descendent doesn't compare equal to its direct ancestor
	// then it should be included in the aggregation. To accomplish this, each
	// parent passes its data to its children to make the comparison.
	//
	// Aggregation gets a little more complicated when peers are considered. If
	// a node's peer has the same length prefix and compare equal then they
	// should be aggregated together. However, it should be aware of their
	// joint direct ancestor and whether they should be aggrated into the
	// ancestor as discussed above.

	// NOTE that we know that BOTH children exist since me.isActive is false. If
	// less than one child existed, the tree would have been compacted to
	// eliminate this node (me).
	left, right := me.children[0], me.children[1]
	leftAggegable, leftData := left.aggregable(data)
	rightAggegable, rightData := right.aggregable(data)

	arePeers := (me.Length+1) == left.Length && left.Length == right.Length
	if arePeers && leftAggegable && rightAggegable && dataEqual(leftData, rightData) {
		return true, leftData
	}
	return false, dataContainer{}
}

// Callback should return true to indicate that iteration should continue or
// false to stop it immediately.
type Callback func(*TrieKey, interface{}) bool

// Iterate walks the entire tree and calls the given function for each active
// node. The order of visiting nodes is essentially lexigraphical:
// - disjoint prefixes are visited in lexigraphical order
// - shorter prefixes are visited immediately before longer prefixes that they contain
func (me *TrieNode) Iterate(callback Callback) bool {
	if me == nil {
		return true
	}

	if me.isActive && callback != nil {
		if !callback(&me.TrieKey, me.Data) {
			return false
		}
	}
	for _, child := range me.children {
		if !child.Iterate(callback) {
			return false
		}
	}
	return true
}

// aggregate is the recursive implementation for Aggregate
// `data`:     the data value from nodes above to use for equal comparison. If
//             the current node is active and its data compares different to
//             this value then its key is not aggregable with containing
//             prefixes.
// `callback`: function to call with each key/data pair found.
func (me *TrieNode) aggregate(data dataContainer, callback Callback) bool {
	if me == nil {
		return true
	}

	aggregable, d := me.aggregable(data)
	if aggregable && !dataEqual(data, d) {
		if callback != nil {
			if !callback(&me.TrieKey, d.data) {
				return false
			}
		}
		for _, child := range me.children {
			if !child.aggregate(d, callback) {
				return false
			}
		}
	} else {
		// Don't visit the current node but descend to children
		for _, child := range me.children {
			if !child.aggregate(data, callback) {
				return false
			}
		}
	}
	return true
}

// Aggregate is like iterate except that it has the capability of aggregating
// prefixes that are either adjacent to each other with the same prefix length
// or contained within another prefix with a shorter length.

// Aggregation visits the minimum set of prefix/data pairs needed to return the
// same data for any longest prefix match as would be returned by the the
// original trie, non-aggregated. This can be useful, for example, to minimize
// the number of prefixes needed to install into a router's datapath to
// guarantee that all of the next hops are correct.
//
// In general, routing protocols should not aggregate and then pass on the
// aggregates to neighbors as this will likely lead to poor comparisions by
// neighboring routers who receive routes aggregated differently from different
// peers.
//
// Prefixes are only considered aggregable if their data compare equal. This is
// useful for aggregating prefixes where the next hop is the same but not where
// they're different.
func (me *TrieNode) Aggregate(callback Callback) bool {
	return me.aggregate(dataContainer{}, callback)
}
