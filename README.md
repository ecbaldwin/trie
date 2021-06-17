This repository contains the low-level data structure for retrieving data based
on the longest prefix match of a given search key against previously inserted
key/datum pairs where the keys are a string of bits and a length telling how
many of the bits in the key are significant.

The first use case is to implement the IPMap in [netaddr].

This data structure that maps to arbitrary data as `interface{}`es. It supports
constant-time basic map operations: insert, get, and remove. It also supports
O(n) iteration over all keys/data pairs in lexigraphical order of keys.

Finally, it also supports a couple of other cool operations.

First, it can efficiently perform a longest prefix match when an exact match is
not available. This operation has the same O(1) \*\* as an exact match.

Second, it supports aggregation of key/values while iterating on the fly. This
has nearly the same O(n) efficiency [^efficiency] as iterating without
aggregating. The rules of aggregation are as follows:

1. The values stored must be comparable. Prefixes get aggregated only where
   their values compare equal.
2. The set of key/value pairs visited is the minimal-size set such that any
   longest prefix match against the aggregated set will always return the same
   value as the same match against the non-aggregated set.
3. The aggregated and non-aggregated sets of keys may be disjoint.

Aggregation can be useful, for example, to minimize the number of prefixes
needed to install into a router's datapath to guarantee that all of the next
hops are correct. In general, though, routing protocols should be careful when
passing aggregated routes to neighbors as this will likely lead to poor
comparisions by neighboring routers who receive routes aggregated differently
from different peers.

A future enhancement could efficiently compute the difference in the aggregated
set when inserting or removing elements so that the entire set doesn't need to
be iterated after each mutation. Since the aggregated set of keys is disjoint
from the original, either operation could result in both adding and removing
key/value pairs. This makes it tricky but it should be possible.

The design for this data-structure is based on the description for BPF trie in
the Linux kernel [bpftrie]. The actual code for the implementation was not
consulted with the except of the definition of structs `lpm_trie_node` and
`lpm_trie`. Otherwise, this is entirely original code.

A go implementation is different enough from it to warrant development from
scratch. It was developed incrementally under new unit tests to ensure that it
is comprehensively tested.

If nothing else, it was super fun to implement.

\*\* There is one complication that may throw its efficiency slightly
     off of O(n) but I haven't analyzed it yet to be sure. It should be pretty
     close.

[netaddr]: https://gopkg.in/netaddr.v1
[bpftrie]: https://github.com/torvalds/linux/blob/94f0b2d4a1/kernel/bpf/lpm_trie.c#L40-L149
