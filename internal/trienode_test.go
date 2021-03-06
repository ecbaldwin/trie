package internal

import (
	"fmt"
	"reflect"
	"testing"
	"unsafe"

	"github.com/stretchr/testify/assert"
)

func minInt(a, b int) int {
	if a < b {
		return a
	}
	return b
}

func TestActive(t *testing.T) {
	var node *TrieNode
	assert.False(t, node.active())
	assert.False(t, (&TrieNode{}).active())
	assert.True(t, (&TrieNode{isActive: true}).active())
}

func TestStructSizes(t *testing.T) {
	// This test has two purposes. The first is to remind any future
	// contributors to be mindful of the size and alignment of these structs
	// and how to measure it. The second is that I'm curious to see if this
	// breaks on any architectures. Like if the go compiler aligns things
	// differently on ARM or whatever. I don't think it will.

	// All the casting to `int` here is because testify didn't consider
	// `uintptr` as comparable and I want to use it for its verbose output on
	// failure. Even if uintptr were comparable, I would have had to cast the
	// constants to uintptr.

	key := TrieKey{}
	keySize := int(unsafe.Sizeof(key))
	keyAlign := int(unsafe.Alignof(key))

	node := TrieNode{}
	nodeSize := int(unsafe.Sizeof(node))
	nodeAlign := int(unsafe.Alignof(node))

	// Why would this ever be more than 8?
	assert.LessOrEqual(t, keyAlign, 8)
	assert.LessOrEqual(t, nodeAlign, 8)

	assert.Equal(t,
		minInt(
			32,
			4*keyAlign,
		),
		keySize,
	)
	assert.Equal(t,
		minInt(
			72,
			keySize+6*keyAlign,
		),
		nodeSize,
	)
}

func TestMatchNilKey(t *testing.T) {
	var trie *TrieNode
	var key *TrieKey

	assert.Nil(t, trie.Match(key))
}

func TestInsertNilKey(t *testing.T) {
	var trie *TrieNode

	newTrie, err := trie.Insert(nil, nil)
	assert.NotNil(t, err)
	assert.Equal(t, trie, newTrie)
	assert.Equal(t, 0, trie.Size())
	assert.Equal(t, 0, trie.height())
}

func TestInsertOrUpdateNilKey(t *testing.T) {
	var trie *TrieNode

	newTrie, err := trie.InsertOrUpdate(nil, nil)
	assert.NotNil(t, err)
	assert.Equal(t, trie, newTrie)
	assert.Equal(t, 0, trie.Size())
	assert.Equal(t, 0, trie.height())
}

func TestInsertOrUpdateChangeValue(t *testing.T) {
	var trie *TrieNode

	key := &TrieKey{}

	trie, err := trie.InsertOrUpdate(key, true)
	assert.Equal(t, 1, trie.Size())
	assert.Nil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))

	trie, err = trie.InsertOrUpdate(key, false)
	assert.Equal(t, 1, trie.Size())
	assert.Nil(t, err)
	assert.False(t, trie.Match(key).Data.(bool))
}

func TestInsertOrUpdateNewKey(t *testing.T) {
	var trie *TrieNode

	key := &TrieKey{}

	trie, err := trie.InsertOrUpdate(key, true)
	assert.Equal(t, 1, trie.Size())
	assert.Nil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))

	newKey := &TrieKey{1, []byte{0}}
	trie, err = trie.InsertOrUpdate(newKey, false)
	assert.Equal(t, 2, trie.Size())
	assert.Nil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))
	assert.False(t, trie.Match(newKey).Data.(bool))
}

func TestInsertOrUpdateNarrowerKey(t *testing.T) {
	var trie *TrieNode

	key := &TrieKey{1, []byte{0}}

	trie, err := trie.InsertOrUpdate(key, true)
	assert.Equal(t, 1, trie.Size())
	assert.Nil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))

	newKey := &TrieKey{}
	trie, err = trie.InsertOrUpdate(newKey, false)
	assert.Equal(t, 2, trie.Size())
	assert.Nil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))
	assert.False(t, trie.Match(newKey).Data.(bool))
}

func TestInsertOrUpdateDisjointKeys(t *testing.T) {
	var trie *TrieNode

	key := &TrieKey{1, []byte{0}}

	trie, err := trie.InsertOrUpdate(key, true)
	assert.Equal(t, 1, trie.Size())
	assert.Nil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))

	newKey := &TrieKey{1, []byte{0x80}}
	trie, err = trie.InsertOrUpdate(newKey, false)
	assert.Equal(t, 2, trie.Size())
	assert.Nil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))
	assert.False(t, trie.Match(newKey).Data.(bool))
}

func TestInsertOrUpdateInactive(t *testing.T) {
	var trie *TrieNode

	key := &TrieKey{1, []byte{0}}

	trie, err := trie.InsertOrUpdate(key, true)
	assert.Equal(t, 1, trie.Size())
	assert.Nil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))

	newKey := &TrieKey{1, []byte{0x80}}
	trie, err = trie.InsertOrUpdate(newKey, false)
	assert.Equal(t, 2, trie.Size())
	assert.Nil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))
	assert.False(t, trie.Match(newKey).Data.(bool))

	inactiveKey := &TrieKey{}
	trie, err = trie.InsertOrUpdate(inactiveKey, "value")
	assert.Equal(t, 3, trie.Size())
	assert.Nil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))
	assert.False(t, trie.Match(newKey).Data.(bool))
	assert.Equal(t, "value", trie.Match(inactiveKey).Data.(string))
}

func TestUpdateNilKey(t *testing.T) {
	var trie *TrieNode

	newTrie, err := trie.Update(nil, nil)
	assert.NotNil(t, err)
	assert.Equal(t, trie, newTrie)
	assert.Equal(t, 0, trie.Size())
	assert.Equal(t, 0, trie.height())
}

func TestUpdateChangeValue(t *testing.T) {
	var trie *TrieNode

	key := &TrieKey{}

	trie, err := trie.Insert(key, true)
	assert.Equal(t, 1, trie.Size())
	assert.Nil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))

	trie, err = trie.Update(key, false)
	assert.Equal(t, 1, trie.Size())
	assert.Nil(t, err)
	assert.False(t, trie.Match(key).Data.(bool))
}

func TestUpdateNewKey(t *testing.T) {
	var trie *TrieNode

	key := &TrieKey{}

	trie, err := trie.Insert(key, true)
	assert.Equal(t, 1, trie.Size())
	assert.Nil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))

	newKey := &TrieKey{1, []byte{0}}
	trie, err = trie.Update(newKey, false)
	assert.Equal(t, 1, trie.Size())
	assert.NotNil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))
	assert.True(t, trie.Match(newKey).Data.(bool))
}

func TestUpdateNarrowerKey(t *testing.T) {
	var trie *TrieNode

	key := &TrieKey{1, []byte{0}}

	trie, err := trie.Insert(key, true)
	assert.Equal(t, 1, trie.Size())
	assert.Nil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))

	newKey := &TrieKey{}
	trie, err = trie.Update(newKey, false)
	assert.Equal(t, 1, trie.Size())
	assert.NotNil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))
	assert.Nil(t, trie.Match(newKey))
}

func TestUpdateDisjointKeys(t *testing.T) {
	var trie *TrieNode

	key := &TrieKey{1, []byte{0}}

	trie, err := trie.Insert(key, true)
	assert.Equal(t, 1, trie.Size())
	assert.Nil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))

	newKey := &TrieKey{1, []byte{0x80}}
	trie, err = trie.Update(newKey, false)
	assert.Equal(t, 1, trie.Size())
	assert.NotNil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))
	assert.Nil(t, trie.Match(newKey))
}

func TestUpdateInactive(t *testing.T) {
	var trie *TrieNode

	key := &TrieKey{1, []byte{0}}

	trie, err := trie.Insert(key, true)
	assert.Equal(t, 1, trie.Size())
	assert.Nil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))

	newKey := &TrieKey{1, []byte{0x80}}
	trie, err = trie.Insert(newKey, false)
	assert.Equal(t, 2, trie.Size())
	assert.Nil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))
	assert.False(t, trie.Match(newKey).Data.(bool))

	inactiveKey := &TrieKey{}
	trie, err = trie.Update(inactiveKey, "value")
	assert.Equal(t, 2, trie.Size())
	assert.NotNil(t, err)
	assert.True(t, trie.Match(key).Data.(bool))
	assert.False(t, trie.Match(newKey).Data.(bool))
	assert.Nil(t, trie.Match(inactiveKey))
}

func TestMatchNilTrie(t *testing.T) {
	var trie *TrieNode

	key := &TrieKey{}
	assert.Nil(t, trie.Match(key))
}

func TestMatchZeroLength(t *testing.T) {
	var trie *TrieNode

	trie, err := trie.Insert(&TrieKey{
		0,
		[]byte{},
	}, nil)
	assert.Nil(t, err)
	assert.True(t, trie.active())
	assert.Equal(t, 1, trie.Size())
	assert.Equal(t, 1, trie.height())

	assert.Equal(t, trie, trie.Match(&TrieKey{
		0,
		[]byte{10, 0, 0, 0},
	}))
}

func TestGetOrInsertNilKey(t *testing.T) {
	var trie *TrieNode

	_, _, err := trie.GetOrInsert(nil, true)
	assert.NotNil(t, err)
}

func TestGetOrInsertTrivial(t *testing.T) {
	var trie *TrieNode
	assert.Equal(t, 0, trie.Size())

	key := &TrieKey{0, []byte{}}

	trie, node, err := trie.GetOrInsert(key, true)
	assert.Nil(t, err)
	assert.Equal(t, 1, trie.Size())
	assert.Equal(t, trie, node)
	assert.True(t, node.Data.(bool))
}

func TestGetOrInsertExists(t *testing.T) {
	var trie *TrieNode

	key := &TrieKey{0, []byte{}}

	trie, err := trie.Insert(key, true)
	assert.Equal(t, 1, trie.Size())

	trie, node, err := trie.GetOrInsert(key, false)

	assert.Nil(t, err)
	assert.Equal(t, 1, trie.Size())
	assert.Equal(t, trie, node)
	assert.True(t, node.Data.(bool))
}

func TestGetOrInsertBroader(t *testing.T) {
	var trie *TrieNode

	existingKey := &TrieKey{16, []byte{10, 224}}
	trie, err := trie.Insert(existingKey, true)
	assert.Equal(t, 1, trie.Size())

	broaderKey := &TrieKey{8, []byte{10}}
	trie, node, err := trie.GetOrInsert(broaderKey, false)

	assert.Nil(t, err)
	assert.Equal(t, 2, trie.Size())
	assert.Equal(t, trie, node)
	assert.False(t, node.Data.(bool))

	assert.True(t, trie.Match(existingKey).Data.(bool))
	assert.False(t, trie.Match(broaderKey).Data.(bool))
}

func TestGetOrInsertNarrower(t *testing.T) {
	var trie *TrieNode

	existingKey := &TrieKey{16, []byte{10, 224}}
	trie, err := trie.Insert(existingKey, true)
	assert.Equal(t, 1, trie.Size())

	narrowerKey := &TrieKey{24, []byte{10, 224, 24}}
	trie, node, err := trie.GetOrInsert(narrowerKey, false)

	fmt.Printf("%+v\n", trie)
	fmt.Printf("%+v\n", node)

	assert.Nil(t, err)
	assert.Equal(t, 2, trie.Size())
	assert.NotEqual(t, trie, node)
	assert.False(t, node.Data.(bool))

	assert.True(t, trie.Match(existingKey).Data.(bool))
	assert.False(t, trie.Match(narrowerKey).Data.(bool))
}

func TestGetOrInsertDisjoint(t *testing.T) {
	var trie *TrieNode

	existingKey := &TrieKey{16, []byte{10, 224}}
	trie, err := trie.Insert(existingKey, true)
	assert.Equal(t, 1, trie.Size())

	disjointKey := &TrieKey{16, []byte{10, 225}}
	trie, node, err := trie.GetOrInsert(disjointKey, false)

	assert.Nil(t, err)
	assert.Equal(t, 2, trie.Size())
	assert.False(t, node.Data.(bool))

	assert.True(t, trie.Match(existingKey).Data.(bool))
	assert.False(t, trie.Match(disjointKey).Data.(bool))
}

func TestGetOrInsertInActive(t *testing.T) {
	var trie *TrieNode

	trie, _ = trie.Insert(&TrieKey{16, []byte{10, 224}}, true)
	trie, _ = trie.Insert(&TrieKey{16, []byte{10, 225}}, true)
	assert.Equal(t, 2, trie.Size())

	trie, node, err := trie.GetOrInsert(&TrieKey{15, []byte{10, 224}}, false)
	assert.Nil(t, err)
	assert.Equal(t, 3, trie.Size())
	assert.Equal(t, trie, node)
	assert.False(t, node.Data.(bool))
}

func TestNoMatchTooBroad(t *testing.T) {
	var trie *TrieNode

	trie, err := trie.Insert(&TrieKey{
		24,
		[]byte{10, 0, 0, 0},
	}, nil)
	assert.Nil(t, err)
	assert.True(t, trie.active())
	assert.Equal(t, 1, trie.Size())
	assert.Equal(t, 1, trie.height())

	assert.Nil(t, trie.Match(&TrieKey{
		23,
		[]byte{10, 0, 0, 0},
	}))
}

func TestNoMatchPrefixMisMatch(t *testing.T) {
	tests := []struct {
		desc         string
		nodePrefix   []byte
		nodeLength   uint
		searchPrefix []byte
		searchLength uint
	}{
		{
			desc:         "full bytes, mismatch in last byte",
			nodePrefix:   []byte{10, 0, 0, 0},
			nodeLength:   24,
			searchPrefix: []byte{10, 0, 1, 0},
			searchLength: 32,
		},
		{
			desc:         "full bytes, mismatch in earlier byte",
			nodePrefix:   []byte{10, 0, 0, 0},
			nodeLength:   24,
			searchPrefix: []byte{10, 1, 0, 0},
			searchLength: 32,
		},
		{
			desc:         "full bytes, mismatch in first byte",
			nodePrefix:   []byte{10, 0, 0, 0},
			nodeLength:   24,
			searchPrefix: []byte{11, 0, 0, 0},
			searchLength: 32,
		},
		{
			desc:         "mismatch in partial byte",
			nodePrefix:   []byte{10, 0, 0, 0},
			nodeLength:   27,
			searchPrefix: []byte{10, 0, 0, 128},
			searchLength: 32,
		},
		{
			desc:         "only one partial byte",
			nodePrefix:   []byte{0},
			nodeLength:   7,
			searchPrefix: []byte{2},
			searchLength: 8,
		},
		{
			desc:         "only one full byte",
			nodePrefix:   []byte{0},
			nodeLength:   8,
			searchPrefix: []byte{10, 0},
			searchLength: 16,
		},
	}

	for _, tt := range tests {
		t.Run(tt.desc, func(t *testing.T) {
			var trie *TrieNode

			trie, err := trie.Insert(&TrieKey{
				tt.nodeLength,
				tt.nodePrefix,
			}, nil)
			assert.Nil(t, err)
			assert.True(t, trie.active())
			assert.Equal(t, 1, trie.Size())
			assert.Equal(t, 1, trie.height())

			assert.Nil(t, trie.Match(&TrieKey{
				tt.searchLength,
				tt.searchPrefix,
			}))
		})
	}
}

func TestMatchSimplePrefixMatch(t *testing.T) {
	tests := []struct {
		desc       string
		nodePrefix []byte
		nodeLength uint
	}{
		{
			desc:       "full bytes, mismatch in last byte",
			nodePrefix: []byte{10, 0, 0, 0},
			nodeLength: 24,
		},
		{
			desc:       "full bytes, mismatch in earlier byte",
			nodePrefix: []byte{10, 0, 0, 0},
			nodeLength: 24,
		},
		{
			desc:       "full bytes, mismatch in first byte",
			nodePrefix: []byte{10, 0, 0, 0},
			nodeLength: 24,
		},
		{
			desc:       "mismatch in partial byte",
			nodePrefix: []byte{10, 0, 0, 0},
			nodeLength: 27,
		},
		{
			desc:       "only one full byte",
			nodePrefix: []byte{0},
			nodeLength: 8,
		},
		{
			desc:       "partial byte",
			nodePrefix: []byte{0xfe},
			nodeLength: 7,
		},
	}

	for _, tt := range tests {
		t.Run(tt.desc, func(t *testing.T) {
			var trie *TrieNode

			key := &TrieKey{
				tt.nodeLength,
				tt.nodePrefix,
			}
			trie, err := trie.Insert(key, nil)
			assert.Nil(t, err)
			assert.Equal(t, 1, trie.Size())
			assert.Equal(t, 1, trie.height())

			assert := assert.New(t)
			assert.Equal(trie, trie.Match(key))
		})
	}
}

func TestMatchPartialByteMatches(t *testing.T) {
	tests := []struct {
		nodePrefix []byte
		nodeLength uint
	}{
		{
			nodePrefix: []byte{0x80},
			nodeLength: 1,
		},
		{
			nodePrefix: []byte{0xc0},
			nodeLength: 2,
		},
		{
			nodePrefix: []byte{0xe0},
			nodeLength: 3,
		},
		{
			nodePrefix: []byte{0xf0},
			nodeLength: 4,
		},
		{
			nodePrefix: []byte{0xf8},
			nodeLength: 5,
		},
		{
			nodePrefix: []byte{0xfc},
			nodeLength: 6,
		},
		{
			nodePrefix: []byte{0xfe},
			nodeLength: 7,
		},
		{
			nodePrefix: []byte{0xff},
			nodeLength: 8,
		},
	}

	for _, tt := range tests {
		t.Run(fmt.Sprintf("%d", tt.nodeLength), func(t *testing.T) {
			var trie *TrieNode

			key := &TrieKey{
				tt.nodeLength,
				tt.nodePrefix,
			}
			trie, err := trie.Insert(key, nil)
			assert.Nil(t, err)
			assert.True(t, trie.active())
			assert.Equal(t, 1, trie.Size())
			assert.Equal(t, 1, trie.height())

			assert := assert.New(t)
			assert.Equal(trie, trie.Match(&TrieKey{
				tt.nodeLength,
				// Always use 0xff to ensure that extraneous bits in the data are ignored
				[]byte{0xff},
			}))

			// byte with 0 in the last bit to match based on nodeLength
			var mismatch byte
			mismatch = 0xff & ^(0x80 >> (tt.nodeLength - 1))

			assert.Nil(trie.Match(&TrieKey{
				tt.nodeLength,
				// Always use a byte with a 0 is the last matched bit
				[]byte{mismatch},
			}))
		})
	}
}

func TestInsertOverlapping(t *testing.T) {
	tests := []struct {
		desc    string
		a, b, c TrieKey
	}{
		{
			desc: "16 and 24",
			a:    TrieKey{16, []byte{10, 200, 0, 0}},
			b:    TrieKey{24, []byte{10, 200, 20, 0}},
			c:    TrieKey{32, []byte{10, 200, 20, 0}},
		},
		{
			desc: "17 and 27",
			a:    TrieKey{17, []byte{10, 200, 0, 0}},
			b:    TrieKey{27, []byte{10, 200, 0, 0xe0}},
			c:    TrieKey{31, []byte{10, 200, 0, 0xf8}},
		},
		{
			desc: "0 and 8",
			a:    TrieKey{0, []byte{}},
			b:    TrieKey{8, []byte{10}},
			c:    TrieKey{16, []byte{10, 10}},
		},
	}

	for _, tt := range tests {
		t.Run(tt.desc, func(t *testing.T) {
			// This test inserts the three given nodes in the order given and
			// checks that they are found in the resulting trie
			subTest := func(first, second, third *TrieKey) func(t *testing.T) {
				return func(t *testing.T) {
					var trie *TrieNode

					trie, err := trie.Insert(first, nil)
					assert.Nil(t, err)
					assert.NotNil(t, trie.Match(first))
					assert.Equal(t, 1, trie.Size())
					assert.Equal(t, 1, trie.height())

					trie, err = trie.Insert(second, nil)
					assert.Nil(t, err)
					assert.NotNil(t, trie.Match(second))
					assert.Equal(t, 2, trie.Size())
					assert.Equal(t, 2, trie.height())

					trie, err = trie.Insert(third, nil)
					assert.Nil(t, err)
					assert.NotNil(t, trie.Match(third))
					assert.Equal(t, 3, trie.Size())
					assert.Equal(t, 3, trie.height())
				}
			}
			t.Run("forward", subTest(&tt.a, &tt.b, &tt.c))
			t.Run("backward", subTest(&tt.c, &tt.b, &tt.a))

			// This sub-test tests that a node cannot be inserted twice
			insertDuplicate := func(key TrieKey) func(t *testing.T) {
				return func(t *testing.T) {
					var trie *TrieNode

					trie, err := trie.Insert(&key, nil)
					assert.Nil(t, err)
					assert.True(t, trie.active())
					assert.NotNil(t, trie)
					assert.Equal(t, 1, trie.Size())
					assert.Equal(t, 1, trie.height())

					dup := key
					newTrie, err := trie.Insert(&dup, nil)
					assert.NotNil(t, err)
					assert.Equal(t, trie, newTrie)
					assert.Equal(t, 1, trie.Size())
					assert.Equal(t, 1, trie.height())
				}
			}
			t.Run("duplicate a", insertDuplicate(tt.a))
			t.Run("duplicate b", insertDuplicate(tt.b))
		})
	}
}

func TestInsertDisjoint(t *testing.T) {
	tests := []struct {
		desc        string
		a, b, super TrieKey
	}{
		{
			desc:  "first bit",
			a:     TrieKey{1, []byte{0}},
			b:     TrieKey{1, []byte{128}},
			super: TrieKey{0, []byte{}},
		},
		{
			desc:  "seventeenth bit",
			a:     TrieKey{17, []byte{10, 224, 0}},
			b:     TrieKey{17, []byte{10, 224, 128}},
			super: TrieKey{16, []byte{10, 224}},
		},
		{
			desc:  "partial b bit",
			a:     TrieKey{23, []byte{10, 224, 0}},
			b:     TrieKey{23, []byte{10, 224, 8}},
			super: TrieKey{20, []byte{10, 224, 0}},
		},
	}

	for _, tt := range tests {
		t.Run(tt.desc, func(t *testing.T) {
			subTest := func(first, second *TrieKey) func(t *testing.T) {
				// This test inserts the two given nodes in the order given and
				// checks that they are both found in the resulting trie
				return func(t *testing.T) {
					var trie *TrieNode

					trie, err := trie.Insert(first, nil)
					assert.Nil(t, err)
					assert.Equal(t, &trie.TrieKey, first)
					assert.Equal(t, 1, trie.Size())
					assert.Equal(t, 1, trie.height())

					trie, err = trie.Insert(second, nil)
					assert.Nil(t, err)
					assert.NotNil(t, trie.Match(second))
					assert.Equal(t, 2, trie.Size())
					assert.Equal(t, 2, trie.height())

					assert.Nil(t, trie.Match(&tt.super))

					// The following are testing a bit more of the internals
					// than I normally do.
					assert.False(t, trie.active())
					assert.Equal(t, trie.TrieKey, tt.super)

					// insert an active node the same as `super` to turn it active
					trie, err = trie.Insert(&tt.super, nil)
					assert.Nil(t, err)
					assert.NotNil(t, trie.Match(&tt.super))
					assert.Equal(t, 3, trie.Size())
					assert.Equal(t, 2, trie.height())
				}
			}
			t.Run("forward", subTest(&tt.a, &tt.b))
			t.Run("backward", subTest(&tt.b, &tt.a))
		})
	}
}

func TestInsertMoreComplex(t *testing.T) {
	tests := []struct {
		desc string
		keys []TrieKey
	}{
		{
			desc: "mix disjoint and overlapping",
			keys: []TrieKey{
				TrieKey{0, []byte{}},
				TrieKey{8, []byte{0xff}},
				TrieKey{8, []byte{0xfe}},
				TrieKey{16, []byte{0xff, 0xff}},
				TrieKey{16, []byte{0xff, 0xfe}},
				TrieKey{17, []byte{0xff, 0xff, 0x00}},
				TrieKey{17, []byte{0xff, 0xfe, 0x80}},
				TrieKey{18, []byte{0xff, 0xfe, 0x80}},
				TrieKey{18, []byte{0xff, 0xff, 0xb0}},
				TrieKey{24, []byte{0xff, 0xfe, 0xbf}},
				TrieKey{24, []byte{0xff, 0xff, 0xbe}},
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.desc, func(t *testing.T) {
			t.Run("forward", func(t *testing.T) {
				var trie *TrieNode

				for _, key := range tt.keys {
					var err error
					trie, err = trie.Insert(&key, nil)
					assert.Nil(t, err)
					assert.NotNil(t, trie.Match(&key))
				}
			})
			t.Run("backward", func(t *testing.T) {
				var trie *TrieNode

				for i := len(tt.keys); i != 0; i-- {
					var err error
					key := tt.keys[i-1]

					trie, err = trie.Insert(&key, nil)
					assert.Nil(t, err)
					assert.NotNil(t, trie.Match(&key))
				}
			})
		})
	}
}

func TestContains(t *testing.T) {
	tests := []struct {
		desc           string
		a, b           *TrieKey
		matches, exact bool
		common, child  uint
	}{
		{
			desc:    "trivial",
			a:       &TrieKey{0, []byte{}},
			b:       &TrieKey{0, []byte{}},
			matches: true,
			exact:   true,
			common:  0,
		},
		{
			desc:    "exact",
			a:       &TrieKey{16, []byte{10, 0}},
			b:       &TrieKey{16, []byte{10, 0}},
			matches: true,
			exact:   true,
			common:  16,
		},
		{
			desc:    "exact partial",
			a:       &TrieKey{19, []byte{10, 0, 0}},
			b:       &TrieKey{19, []byte{10, 0, 0x1f}},
			matches: true,
			exact:   true,
			common:  19,
		},
		{
			desc:    "empty prefix match",
			a:       &TrieKey{0, []byte{}},
			b:       &TrieKey{16, []byte{10, 10}},
			matches: true,
			exact:   false,
			common:  0,
			child:   0,
		},
		{
			desc:    "empty prefix match backwards",
			a:       &TrieKey{0, []byte{}},
			b:       &TrieKey{16, []byte{130, 10}},
			matches: true,
			exact:   false,
			common:  0,
			child:   1,
		},
		{
			desc:    "matches",
			a:       &TrieKey{8, []byte{10}},
			b:       &TrieKey{16, []byte{10, 10}},
			matches: true,
			exact:   false,
			common:  8,
			child:   0,
		},
		{
			desc:    "matches partial",
			a:       &TrieKey{9, []byte{10, 200}},
			b:       &TrieKey{16, []byte{10, 129}},
			matches: true,
			exact:   false,
			common:  9,
			child:   0,
		},
		{
			desc:    "matches backwards",
			a:       &TrieKey{8, []byte{10}},
			b:       &TrieKey{16, []byte{10, 200}},
			matches: true,
			exact:   false,
			common:  8,
			child:   1,
		},
		{
			desc:    "matches backwards partial",
			a:       &TrieKey{9, []byte{10, 240}},
			b:       &TrieKey{16, []byte{10, 200}},
			matches: true,
			exact:   false,
			common:  9,
			child:   1,
		},
		{
			desc:    "disjoint",
			a:       &TrieKey{1, []byte{0}},
			b:       &TrieKey{1, []byte{128}},
			matches: false,
			common:  0,
			child:   1,
		},
		{
			desc:    "disjoint longer",
			a:       &TrieKey{17, []byte{0, 0, 0}},
			b:       &TrieKey{17, []byte{0, 0, 128}},
			matches: false,
			common:  16,
			child:   1,
		},
		{
			desc:    "disjoint longer partial",
			a:       &TrieKey{17, []byte{0, 0, 0}},
			b:       &TrieKey{17, []byte{0, 1, 0}},
			matches: false,
			common:  15,
			child:   1,
		},
		{
			desc:    "disjoint backwards",
			a:       &TrieKey{1, []byte{128}},
			b:       &TrieKey{1, []byte{0}},
			matches: false,
			common:  0,
			child:   0,
		},
		{
			desc:    "disjoint backwards longer",
			a:       &TrieKey{19, []byte{0, 0, 128}},
			b:       &TrieKey{19, []byte{0, 0, 0}},
			matches: false,
			common:  16,
			child:   0,
		},
		{
			desc:    "disjoint backwards longer partial",
			a:       &TrieKey{19, []byte{0, 1, 0}},
			b:       &TrieKey{19, []byte{0, 0, 0}},
			matches: false,
			common:  15,
			child:   0,
		},
		{
			desc:    "disjoint with common",
			a:       &TrieKey{16, []byte{10, 0}},
			b:       &TrieKey{16, []byte{10, 10}},
			matches: false,
			common:  12,
			child:   1,
		},
		{
			desc:    "disjoint with more disjoint bytes",
			a:       &TrieKey{24, []byte{0, 255, 255}},
			b:       &TrieKey{24, []byte{128, 0, 0}},
			matches: false,
			common:  0,
			child:   1,
		},
	}

	for _, tt := range tests {
		t.Run(tt.desc, func(t *testing.T) {
			matches, exact, common, child := contains(tt.a, tt.b, 0)
			assert.Equal(t, tt.matches, matches)
			assert.Equal(t, tt.exact, exact)
			assert.Equal(t, tt.common, common)
			assert.Equal(t, tt.child, child)

			// Opportunistically test the compare function
			t.Run("compare forward", func(t *testing.T) {
				_, _, reversed, _, _ := compare(tt.a, tt.b, 0)
				assert.False(t, reversed)
			})
			t.Run("compare reversed", func(t *testing.T) {
				_, _, reversed, _, _ := compare(tt.b, tt.a, 0)
				assert.Equal(t, tt.a.Length != tt.b.Length, reversed)
			})
		})
	}
}

func TestBitsToBytes(t *testing.T) {
	tests := []struct {
		bits, bytes uint
	}{
		{bits: 0, bytes: 0},
		{bits: 1, bytes: 1},
		{bits: 8, bytes: 1},
		{bits: 9, bytes: 2},
		{bits: 16, bytes: 2},
		{bits: 17, bytes: 3},
		{bits: 24, bytes: 3},
		{bits: 25, bytes: 4},
		{bits: 32, bytes: 4},
		{bits: 33, bytes: 5},
		{bits: 40, bytes: 5},
		{bits: 41, bytes: 6},
		{bits: 48, bytes: 6},
		{bits: 49, bytes: 7},
		{bits: 64, bytes: 8},
		{bits: 65, bytes: 9},
		{bits: 128, bytes: 16},
		{bits: 129, bytes: 17},
		{bits: 256, bytes: 32},
		{bits: 257, bytes: 33},
		{bits: 512, bytes: 64},
		{bits: 513, bytes: 65},
		{bits: 1024, bytes: 128},
		{bits: 1025, bytes: 129},
		{bits: 4096, bytes: 512},
		{bits: 4097, bytes: 513},
	}

	for _, tt := range tests {
		t.Run(fmt.Sprintf("%d", tt.bits), func(t *testing.T) {
			assert.Equal(t, tt.bytes, bitsToBytes(tt.bits))
		})
	}
}

func TestDeleteFromNilTree(t *testing.T) {
	var trie *TrieNode

	key := TrieKey{
		0,
		[]byte{},
	}
	trie, err := trie.Delete(&key)
	assert.Nil(t, trie)
	assert.NotNil(t, err)
}

func TestDeleteNilKey(t *testing.T) {
	var trie *TrieNode

	key := TrieKey{
		0,
		[]byte{},
	}
	trie, err := trie.Insert(&key, nil)
	assert.Nil(t, err)
	assert.Equal(t, 1, trie.Size())

	trie, err = trie.Delete(nil)
	assert.NotNil(t, err)
}

func TestDeleteSimple(t *testing.T) {
	var trie *TrieNode

	key := TrieKey{
		24,
		[]byte{172, 16, 200, 0},
	}
	trie, err := trie.Insert(&key, nil)
	trie, err = trie.Delete(&key)
	assert.Nil(t, err)
	assert.Nil(t, trie)
}

func TestDeleteLeftChild(t *testing.T) {
	var trie *TrieNode

	key := TrieKey{
		24,
		[]byte{172, 16, 200, 0},
	}
	trie, err := trie.Insert(&key, nil)
	childKey := TrieKey{
		25,
		[]byte{172, 16, 200, 0},
	}
	trie, err = trie.Insert(&childKey, nil)
	trie, err = trie.Delete(&key)
	assert.Nil(t, err)
	assert.NotNil(t, trie)

	assert.Nil(t, trie.Match(&key))
	assert.NotNil(t, trie.Match(&childKey))
}

func TestDeleteRightChild(t *testing.T) {
	var trie *TrieNode

	key := TrieKey{
		24,
		[]byte{172, 16, 200, 0},
	}
	trie, err := trie.Insert(&key, nil)
	childKey := &TrieKey{
		25,
		[]byte{172, 16, 200, 128},
	}
	trie, err = trie.Insert(childKey, nil)
	trie, err = trie.Delete(&key)
	assert.Nil(t, err)
	assert.NotNil(t, trie)

	assert.Nil(t, trie.Match(&key))
	assert.NotNil(t, trie.Match(childKey))
}

func TestDeleteBothChildren(t *testing.T) {
	var trie *TrieNode

	key := TrieKey{
		24,
		[]byte{172, 16, 200, 0},
	}
	trie, err := trie.Insert(&key, nil)
	leftChild := &TrieKey{
		25,
		[]byte{172, 16, 200, 0},
	}
	trie, err = trie.Insert(leftChild, nil)
	rightChild := &TrieKey{
		25,
		[]byte{172, 16, 200, 128},
	}
	trie, err = trie.Insert(rightChild, nil)
	trie, err = trie.Delete(&key)
	assert.Nil(t, err)
	assert.NotNil(t, trie)

	assert.Nil(t, trie.Match(&key))
	assert.NotNil(t, trie.Match(leftChild))
	assert.NotNil(t, trie.Match(rightChild))
}

func TestDeleteRecursiveNil(t *testing.T) {
	var trie *TrieNode

	key := TrieKey{
		24,
		[]byte{172, 16, 200, 0},
	}
	trie, err := trie.Insert(&key, nil)
	childKey := TrieKey{
		25,
		[]byte{172, 16, 200, 0},
	}
	trie, err = trie.Delete(&childKey)
	assert.NotNil(t, err)
	assert.NotNil(t, trie)

	assert.NotNil(t, trie.Match(&key))
	match := trie.Match(&childKey)
	assert.NotEqual(t, childKey, match.TrieKey)
	// assert.Nil(t, trie.Get(&childKey))
}

func TestDeleteRecursiveLeftChild(t *testing.T) {
	// NOTE: There's no specific test for other child combinations because I
	// didn't feel it added much. It uses already well-tested code paths.
	var trie *TrieNode

	key := TrieKey{
		24,
		[]byte{172, 16, 200, 0},
	}
	trie, err := trie.Insert(&key, nil)
	childKey := &TrieKey{
		25,
		[]byte{172, 16, 200, 0},
	}
	trie, err = trie.Insert(childKey, nil)
	trie, err = trie.Delete(childKey)
	assert.Nil(t, err)
	assert.NotNil(t, trie)

	assert.NotNil(t, trie.Match(&key))
	match := trie.Match(childKey)
	assert.NotEqual(t, *childKey, match.TrieKey)
	// assert.Nil(t, trie.Get(childKey))
}

func TestDeleteKeyTooBroad(t *testing.T) {
	var trie *TrieNode

	key := TrieKey{
		25,
		[]byte{172, 16, 200, 0},
	}
	trie, err := trie.Insert(&key, nil)

	broadKey := TrieKey{
		24,
		[]byte{172, 16, 200, 0},
	}
	trie, err = trie.Delete(&broadKey)
	assert.NotNil(t, err)
	assert.NotNil(t, trie)

	assert.NotNil(t, trie.Match(&key))
	assert.Nil(t, trie.Match(&broadKey))
}

func TestDeleteKeyDisjoint(t *testing.T) {
	var trie *TrieNode

	key := TrieKey{
		25,
		[]byte{172, 16, 200, 0},
	}
	trie, err := trie.Insert(&key, nil)

	disjointKey := TrieKey{
		25,
		[]byte{172, 16, 200, 128},
	}
	trie, err = trie.Delete(&disjointKey)
	assert.NotNil(t, err)
	assert.NotNil(t, trie)

	assert.NotNil(t, trie.Match(&key))
	assert.Nil(t, trie.Match(&disjointKey))
}

func TestSuccessivelyBetter(t *testing.T) {
	var trie *TrieNode

	keys := []TrieKey{
		TrieKey{0, []byte{10, 224, 24, 0}},
		TrieKey{1, []byte{10, 224, 24, 0}},
		TrieKey{8, []byte{10, 224, 24, 0}},
		TrieKey{12, []byte{10, 224, 24, 0}},
		TrieKey{16, []byte{10, 224, 24, 0}},
		TrieKey{18, []byte{10, 224, 24, 0}},
		TrieKey{20, []byte{10, 224, 24, 0}},
		TrieKey{21, []byte{10, 224, 24, 0}},
		TrieKey{22, []byte{10, 224, 24, 0}},
		TrieKey{24, []byte{10, 224, 24, 0}},
		TrieKey{27, []byte{10, 224, 24, 0}},
		TrieKey{30, []byte{10, 224, 24, 0}},
		TrieKey{32, []byte{10, 224, 24, 0}},
	}

	// Add successively more specific keys to the trie and assert that exact
	// matches are returned when appropriate and non-exact, but longest matches
	// are returned for the rest.
	for index, key := range keys {
		var err error
		trie, err = trie.Insert(&key, nil)
		assert.Nil(t, err)
		assert.Equal(t, index+1, trie.Size())
		assert.Equal(t, index+1, trie.height())

		for i, searchKey := range keys {
			node := trie.Match(&searchKey)
			assert.NotNil(t, node)
			if i <= index {
				assert.Equal(t, searchKey, node.TrieKey)
			} else {
				assert.Equal(t, keys[index], node.TrieKey)
			}
		}
	}
	// Delete the nodes in the same order they were added and check that the
	// broader keys are no longer found in the trie as they're deleted but
	// the more specific ones are still found.
	for index, key := range keys {
		var err error
		trie, err = trie.Delete(&key)
		assert.Nil(t, err)
		assert.Equal(t, len(keys)-index-1, trie.Size())
		assert.Equal(t, len(keys)-index-1, trie.height())

		for i, searchKey := range keys {
			node := trie.Match(&searchKey)
			if i <= index {
				assert.Nil(t, node)
			} else {
				assert.Equal(t, node.TrieKey, searchKey)
			}
		}
	}
}

func TestIterate(t *testing.T) {
	keys := []TrieKey{
		TrieKey{20, []byte{172, 21, 0, 0}},
		TrieKey{25, []byte{192, 68, 27, 0}},
		TrieKey{25, []byte{192, 168, 26, 128}},
		TrieKey{32, []byte{10, 224, 24, 0}},
		TrieKey{24, []byte{192, 68, 24, 0}},
		TrieKey{12, []byte{172, 16, 0, 0}},
		TrieKey{24, []byte{192, 68, 26, 0}},
		TrieKey{30, []byte{10, 224, 24, 0}},
		TrieKey{24, []byte{192, 168, 24, 0}},
		TrieKey{24, []byte{192, 168, 25, 0}},
		TrieKey{25, []byte{192, 168, 26, 0}},
		TrieKey{24, []byte{192, 68, 25, 0}},
		TrieKey{24, []byte{192, 168, 27, 0}},
		TrieKey{19, []byte{172, 20, 128, 0}},
		TrieKey{25, []byte{192, 68, 27, 128}},
	}

	golden := []TrieKey{
		TrieKey{30, []byte{10, 224, 24, 0}},
		TrieKey{32, []byte{10, 224, 24, 0}},
		TrieKey{12, []byte{172, 16, 0, 0}},
		TrieKey{19, []byte{172, 20, 128, 0}},
		TrieKey{20, []byte{172, 21, 0, 0}},
		TrieKey{24, []byte{192, 68, 24, 0}},
		TrieKey{24, []byte{192, 68, 25, 0}},
		TrieKey{24, []byte{192, 68, 26, 0}},
		TrieKey{25, []byte{192, 68, 27, 0}},
		TrieKey{25, []byte{192, 68, 27, 128}},
		TrieKey{24, []byte{192, 168, 24, 0}},
		TrieKey{24, []byte{192, 168, 25, 0}},
		TrieKey{25, []byte{192, 168, 26, 0}},
		TrieKey{25, []byte{192, 168, 26, 128}},
		TrieKey{24, []byte{192, 168, 27, 0}},
	}

	var trie *TrieNode
	check := func(t *testing.T) {
		result := []TrieKey{}
		trie.Iterate(func(key *TrieKey, _ interface{}) bool {
			result = append(result, *key)
			return true
		})
		assert.Equal(t, golden, result)

		iterations := 0
		trie.Iterate(func(key *TrieKey, _ interface{}) bool {
			iterations++
			return false
		})
		assert.Equal(t, 1, iterations)

		// Just ensure that iterating with a nil callback doesn't crash
		trie.Iterate(nil)
	}

	t.Run("normal insert", func(t *testing.T) {
		trie = nil
		for _, key := range keys {
			trie, _ = trie.Insert(&key, nil)
		}
		check(t)
	})
	t.Run("get or insert", func(t *testing.T) {
		trie = nil
		for _, key := range keys {
			var err error
			trie, _, err = trie.GetOrInsert(&key, nil)
			assert.Nil(t, err)
		}
		check(t)
	})
}

type pair struct {
	key  TrieKey
	data interface{}
}

func printTrie(trie *TrieNode) {
	var recurse func(trie *TrieNode, level int)

	recurse = func(trie *TrieNode, level int) {
		if trie == nil {
			return
		}
		for i := 0; i < level; i++ {
			fmt.Printf("    ")
		}
		fmt.Printf("%+v\n", trie)
		recurse(trie.children[0], level+1)
		recurse(trie.children[1], level+1)
	}

	recurse(trie, 0)
}

func TestAggregate(t *testing.T) {
	tests := []struct {
		desc   string
		pairs  []pair
		golden []pair
	}{
		{
			desc:   "nothing",
			pairs:  []pair{},
			golden: []pair{},
		},
		{
			desc: "simple aggregation",
			pairs: []pair{
				pair{key: TrieKey{31, []byte{10, 224, 24, 2}}},
				pair{key: TrieKey{32, []byte{10, 224, 24, 1}}},
				pair{key: TrieKey{32, []byte{10, 224, 24, 0}}},
			},
			golden: []pair{
				pair{key: TrieKey{30, []byte{10, 224, 24, 0}}},
			},
		},
		{
			desc: "same as iterate",
			pairs: []pair{
				pair{key: TrieKey{20, []byte{172, 21, 0, 0}}},
				pair{key: TrieKey{25, []byte{192, 68, 27, 0}}},
				pair{key: TrieKey{25, []byte{192, 168, 26, 128}}},
				pair{key: TrieKey{32, []byte{10, 224, 24, 0}}},
				pair{key: TrieKey{24, []byte{192, 68, 24, 0}}},
				pair{key: TrieKey{12, []byte{172, 16, 0, 0}}},
				pair{key: TrieKey{24, []byte{192, 68, 26, 0}}},
				pair{key: TrieKey{30, []byte{10, 224, 24, 0}}},
				pair{key: TrieKey{24, []byte{192, 168, 24, 0}}},
				pair{key: TrieKey{24, []byte{192, 168, 25, 0}}},
				pair{key: TrieKey{25, []byte{192, 168, 26, 0}}},
				pair{key: TrieKey{24, []byte{192, 68, 25, 0}}},
				pair{key: TrieKey{24, []byte{192, 168, 27, 0}}},
				pair{key: TrieKey{19, []byte{172, 20, 128, 0}}},
				pair{key: TrieKey{25, []byte{192, 68, 27, 128}}},
			},
			golden: []pair{
				pair{key: TrieKey{30, []byte{10, 224, 24, 0}}},
				pair{key: TrieKey{12, []byte{172, 16, 0, 0}}},
				pair{key: TrieKey{22, []byte{192, 68, 24}}},
				pair{key: TrieKey{22, []byte{192, 168, 24}}},
			},
		},
		{
			desc: "mixed umbrellas",
			pairs: []pair{
				pair{key: TrieKey{30, []byte{10, 224, 24, 0}}, data: true},
				pair{key: TrieKey{31, []byte{10, 224, 24, 0}}, data: false},
				pair{key: TrieKey{32, []byte{10, 224, 24, 1}}, data: true},
				pair{key: TrieKey{32, []byte{10, 224, 24, 0}}, data: false},
			},
			golden: []pair{
				pair{key: TrieKey{30, []byte{10, 224, 24, 0}}, data: true},
				pair{key: TrieKey{31, []byte{10, 224, 24, 0}}, data: false},
				pair{key: TrieKey{32, []byte{10, 224, 24, 1}}, data: true},
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.desc, func(t *testing.T) {
			var trie *TrieNode
			check := func(t *testing.T) {
				expectedIterations := 0
				result := []pair{}
				trie.Aggregate(
					func(key *TrieKey, data interface{}) bool {
						result = append(result, pair{key: *key, data: data})
						expectedIterations = 1
						return true
					},
				)
				assert.Equal(t, tt.golden, result)

				iterations := 0
				trie.Aggregate(
					func(key *TrieKey, data interface{}) bool {
						result = append(result, pair{key: *key, data: data})
						iterations++
						return false
					},
				)
				assert.Equal(t, expectedIterations, iterations)
			}

			t.Run("normal insert", func(t *testing.T) {
				for _, p := range tt.pairs {
					trie, _ = trie.Insert(&p.key, p.data)
				}
				check(t)
			})
			t.Run("get or insert", func(t *testing.T) {
				for _, p := range tt.pairs {
					var err error
					trie, _, err = trie.GetOrInsert(&p.key, p.data)
					assert.Nil(t, err)
				}
				check(t)
			})
		})
	}
}

type comparable struct {
	// Begin with a type (slice) that is not comparable with standard ==
	data []string
}

func (me *comparable) EqualInterface(other interface{}) bool {
	return reflect.DeepEqual(me, other)
}

// Like the TestAggregate above but using a type that is comparable through the
// EqualComparable interface.
func TestAggregateEqualComparable(t *testing.T) {
	NextHop1 := &comparable{data: []string{"10.224.24.1"}}
	NextHop2 := &comparable{data: []string{"10.224.24.111"}}
	tests := []struct {
		desc   string
		pairs  []pair
		golden []pair
	}{
		{
			desc: "mixed umbrellas",
			pairs: []pair{
				pair{key: TrieKey{30, []byte{10, 224, 24, 0}}, data: NextHop1},
				pair{key: TrieKey{31, []byte{10, 224, 24, 0}}, data: NextHop2},
				pair{key: TrieKey{32, []byte{10, 224, 24, 1}}, data: NextHop1},
				pair{key: TrieKey{32, []byte{10, 224, 24, 0}}, data: NextHop2},
			},
			golden: []pair{
				pair{key: TrieKey{30, []byte{10, 224, 24, 0}}, data: NextHop1},
				pair{key: TrieKey{31, []byte{10, 224, 24, 0}}, data: NextHop2},
				pair{key: TrieKey{32, []byte{10, 224, 24, 1}}, data: NextHop1},
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.desc, func(t *testing.T) {
			var trie *TrieNode
			for _, p := range tt.pairs {
				trie, _ = trie.Insert(&p.key, p.data)
			}

			result := []pair{}
			trie.Aggregate(
				func(key *TrieKey, data interface{}) bool {
					result = append(result, pair{key: *key, data: data})
					return true
				},
			)
			assert.Equal(t, tt.golden, result)
		})
	}
}
