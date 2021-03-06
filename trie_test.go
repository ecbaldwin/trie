package trie

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestInsert(t *testing.T) {
	t.Run("Nil", func(t *testing.T) {
		var trie Trie
		assert.Equal(t, 0, trie.Size())

		err := trie.Insert(nil, true)
		assert.NotNil(t, err)
		assert.Equal(t, 0, trie.Size())
	})
	t.Run("Success", func(t *testing.T) {
		var trie Trie
		assert.Equal(t, 0, trie.Size())

		key := &Key{24, []byte("key")}
		err := trie.Insert(key, true)
		assert.Nil(t, err)
		assert.Equal(t, 1, trie.Size())
	})
	t.Run("Success then nil", func(t *testing.T) {
		var trie Trie
		assert.Equal(t, 0, trie.Size())
		key := &Key{24, []byte("key")}
		err := trie.Insert(key, true)
		assert.Equal(t, 1, trie.Size())

		err = trie.Insert(nil, true)
		assert.NotNil(t, err)
		assert.Equal(t, 1, trie.Size())
	})
}

func TestInsertOrUpdate(t *testing.T) {
	t.Run("Nil", func(t *testing.T) {
		var trie Trie
		assert.Equal(t, 0, trie.Size())

		err := trie.InsertOrUpdate(nil, true)
		assert.NotNil(t, err)
		assert.Equal(t, 0, trie.Size())
	})
	t.Run("Success", func(t *testing.T) {
		var trie Trie
		assert.Equal(t, 0, trie.Size())

		key := &Key{24, []byte("key")}
		err := trie.InsertOrUpdate(key, true)
		assert.Nil(t, err)
		assert.Equal(t, 1, trie.Size())
		match, matchedKey, value := trie.Match(key)
		assert.Equal(t, MatchExact, match)
		assert.Equal(t, key, matchedKey)
		assert.True(t, value.(bool))

		err = trie.InsertOrUpdate(key, false)
		assert.Nil(t, err)
		assert.Equal(t, 1, trie.Size())
		match, matchedKey, value = trie.Match(key)
		assert.Equal(t, MatchExact, match)
		assert.Equal(t, key, matchedKey)
		assert.False(t, value.(bool))
	})
	t.Run("Success then nil", func(t *testing.T) {
		var trie Trie
		assert.Equal(t, 0, trie.Size())
		key := &Key{24, []byte("key")}
		err := trie.InsertOrUpdate(key, true)
		assert.Equal(t, 1, trie.Size())

		err = trie.InsertOrUpdate(nil, true)
		assert.NotNil(t, err)
		assert.Equal(t, 1, trie.Size())
	})
}

func TestUpdate(t *testing.T) {
	t.Run("Nil", func(t *testing.T) {
		var trie Trie
		assert.Equal(t, 0, trie.Size())

		err := trie.Update(nil, true)
		assert.NotNil(t, err)
		assert.Equal(t, 0, trie.Size())
	})
	t.Run("Success", func(t *testing.T) {
		var trie Trie
		assert.Equal(t, 0, trie.Size())

		key := &Key{24, []byte("key")}
		trie.Insert(key, false)

		err := trie.Update(key, true)
		assert.Nil(t, err)
		assert.Equal(t, 1, trie.Size())
		match, matchedKey, value := trie.Match(key)
		assert.Equal(t, MatchExact, match)
		assert.Equal(t, key, matchedKey)
		assert.True(t, value.(bool))

		err = trie.Update(key, false)
		assert.Nil(t, err)
		assert.Equal(t, 1, trie.Size())
		match, matchedKey, value = trie.Match(key)
		assert.Equal(t, MatchExact, match)
		assert.Equal(t, key, matchedKey)
		assert.False(t, value.(bool))
	})
	t.Run("Success then nil", func(t *testing.T) {
		var trie Trie
		assert.Equal(t, 0, trie.Size())
		key := &Key{24, []byte("key")}
		trie.Insert(key, false)

		err := trie.Update(key, true)
		assert.Equal(t, 1, trie.Size())

		err = trie.Update(nil, true)
		assert.NotNil(t, err)
		assert.Equal(t, 1, trie.Size())
	})
}

func TestGetOrInsert(t *testing.T) {
	t.Run("Nil", func(t *testing.T) {
		var trie Trie
		assert.Equal(t, 0, trie.Size())

		value, err := trie.GetOrInsert(nil, true)
		assert.NotNil(t, err)
		assert.Nil(t, value)
		assert.Equal(t, 0, trie.Size())
	})
	t.Run("Success", func(t *testing.T) {
		var trie Trie
		assert.Equal(t, 0, trie.Size())

		key := &Key{24, []byte("key")}
		value, err := trie.GetOrInsert(key, true)
		assert.Nil(t, err)
		assert.True(t, value.(bool))
		assert.Equal(t, 1, trie.Size())
	})
	t.Run("Success then nil", func(t *testing.T) {
		var trie Trie
		assert.Equal(t, 0, trie.Size())
		key := &Key{24, []byte("key")}
		err := trie.Insert(key, true)
		assert.Equal(t, 1, trie.Size())

		value, err := trie.GetOrInsert(nil, true)
		assert.NotNil(t, err)
		assert.Nil(t, value)
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
	trie.Iterate(func(key *Key, value interface{}) bool {
		assert.Equal(t, insertKey, key)
		assert.True(t, value.(bool))
		found = true
		return true
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
	trie.Aggregate(func(key *Key, value interface{}) bool {
		assert.Equal(t, insertKey, key)
		assert.True(t, value.(bool))
		found = true
		return true
	})
	assert.True(t, found)
}
