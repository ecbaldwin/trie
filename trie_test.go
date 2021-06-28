package trie

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestInsert(t *testing.T) {
	var trie Trie
	assert.Equal(t, 0, trie.Size())

	t.Run("Nil", func(t *testing.T) {
		err := trie.Insert(nil, true)
		assert.NotNil(t, err)
		assert.Equal(t, 0, trie.Size())
	})
	t.Run("Success", func(t *testing.T) {
		key := &Key{24, []byte("key")}
		err := trie.Insert(key, true)
		assert.Nil(t, err)
		assert.Equal(t, 1, trie.Size())
	})
}

func TestMatch(t *testing.T) {
	var trie Trie

	insertKey := &Key{24, []byte("key")}
	trie.Insert(insertKey, true)

	t.Run("None", func(t *testing.T) {
		level, key, value := trie.Match(&Key{24, []byte("kei")})
		assert.Equal(t, MatchNone, level)
		assert.Nil(t, key)
		assert.Nil(t, value)
	})

	t.Run("Exact", func(t *testing.T) {
		level, key, value := trie.Match(&Key{24, []byte("key")})
		assert.Equal(t, MatchExact, level)
		assert.Equal(t, insertKey, key)
		assert.True(t, value.(bool))
	})

	t.Run("Contains", func(t *testing.T) {
		level, key, value := trie.Match(&Key{32, []byte("keyy")})
		assert.Equal(t, MatchContains, level)
		assert.Equal(t, insertKey, key)
		assert.True(t, value.(bool))
	})
}

func TestDelete(t *testing.T) {
	t.Run("Success", func(t *testing.T) {
		var trie Trie

		insertKey := &Key{24, []byte("key")}
		trie.Insert(insertKey, true)

		key := &Key{24, []byte("key")}
		err := trie.Delete(key)
		assert.Nil(t, err)
		assert.Equal(t, 0, trie.Size())
	})

	t.Run("Not Found", func(t *testing.T) {
		var trie Trie

		insertKey := &Key{24, []byte("key")}
		trie.Insert(insertKey, true)

		key := &Key{24, []byte("kei")}
		err := trie.Delete(key)
		assert.NotNil(t, err)
		assert.Equal(t, 1, trie.Size())
	})

	t.Run("Not Exact", func(t *testing.T) {
		var trie Trie

		insertKey := &Key{24, []byte("key")}
		trie.Insert(insertKey, true)

		key := &Key{32, []byte("keyy")}
		err := trie.Delete(key)
		assert.NotNil(t, err)
		assert.Equal(t, 1, trie.Size())
	})
}

func TestIterate(t *testing.T) {
	var trie Trie

	insertKey := &Key{24, []byte("key")}
	trie.Insert(insertKey, true)

	found := false
	trie.Iterate(func(key *Key, value interface{}) {
		assert.Equal(t, insertKey, key)
		assert.True(t, value.(bool))
		found = true
	})
	assert.True(t, found)
}

func TestAggregate(t *testing.T) {
	var trie Trie

	insertKey := &Key{24, []byte("key")}
	trie.Insert(insertKey, true)

	secondKey := &Key{32, []byte("keyy")}
	trie.Insert(secondKey, true)

	found := false
	trie.Aggregate(func(key *Key, value interface{}) {
		assert.Equal(t, insertKey, key)
		assert.True(t, value.(bool))
		found = true
	})
	assert.True(t, found)
}
