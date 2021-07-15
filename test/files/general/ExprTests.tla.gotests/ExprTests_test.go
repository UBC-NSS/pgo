package exprtests

import (
	"testing"
)

func TestTest1(t *testing.T) {
	result := Test1(Constants{})
	actualStr := result.String()
	expectedStr := "{1, 2, 3}"
	if actualStr != expectedStr {
		t.Errorf("Expected value %s, got %s", expectedStr, actualStr)
	}
}
