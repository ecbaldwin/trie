package trie

import (
	"github.com/ecbaldwin/trie/internal"
)

type Key internal.TrieKey

type Trie struct {
	top *internal.TrieNode
}

// Size returns the number of entries
func (me *Trie) Size() int {
	return me.top.Size()
}

// Insert adds the given key / value pair. If the new key cannot be inserted or
// already exists, an error is returned.
func (me *Trie) Insert(key *Key, value interface{}) error {
	var err error
	me.top, err = me.top.Insert((*internal.TrieKey)(key), value)
	return err
}

// Match indicates how closely the given key matches the search result.
type Match int

const (
	// MatchNone means no existing key matches the given key with a longest-prefix match
	MatchNone Match = iota
	// MatchContains means an existing key matches the given key with a longest-prefix match but not exactly
	MatchContains
	// MatchExact mean an existing key matches the given key exactly
	MatchExact
)

// Match returns the existing key / value pair with the longest prefix that
// fully contains the given key or nil if none match.
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
func (me *Trie) Match(key *Key) (Match, *Key, interface{}) {
	var node *internal.TrieNode
	node = me.top.Match((*internal.TrieKey)(key))
	if node == nil {
		return MatchNone, nil, nil
	}

	var resultKey Key
	resultKey = (Key)(node.TrieKey)

	var match Match
	if node.TrieKey.Length == key.Length {
		match = MatchExact
	} else {
		match = MatchContains
	}
	return match, &resultKey, node.Data
}

// Delete removes a key from the trie with its associated value.
func (me *Trie) Delete(key *Key) error {
	var err error
	me.top, err = me.top.Delete((*internal.TrieKey)(key))
	return err
}

type Callback func(*Key, interface{})

// Iterate walks the entire trie and calls the given function for each key /
// value pair. The order of visiting nodes is essentially lexigraphical:
// - disjoint prefixes are visited in lexigraphical order
// - shorter prefixes are visited immediately before longer prefixes that they contain
func (me *Trie) Iterate(callback Callback) {
	me.top.Iterate(func(key *internal.TrieKey, value interface{}) {
		callback((*Key)(key), value)
	})
}

// Aggregate is like iterate except that it has the capability of aggregating
// prefixes that are either adjacent to each other with the same prefix length
// or contained within another prefix with a shorter length.

// Aggregation visits the minimum set of key/value pairs needed to return the
// same value for any longest prefix match as would be returned by the the
// original trie, non-aggregated. This can be useful, for example, to minimize
// the number of prefixes needed to install into a router's datapath to
// guarantee that all of the next hops are correct.
//
// In general, routing protocols should not aggregate and then pass on the
// aggregates to neighbors as this will likely lead to poor comparisions by
// neighboring routers who receive routes aggregated differently from different
// peers.
//
// Prefixes are only considered aggregable if their value compare equal. This is
// useful for aggregating prefixes where the next hop is the same but not where
// they're different.
func (me *Trie) Aggregate(callback Callback) {
	me.top.Aggregate(func(key *internal.TrieKey, value interface{}) {
		callback((*Key)(key), value)
	})
}
