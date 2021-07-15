package distsys

import "testing"

func TestIntArgument(t *testing.T) {
	processName, argument := ParseProcessId("P(1)")
	if processName != "P" {
		t.Errorf("Expected P, found %s", processName)
	}
	if argument != "1" {
		t.Errorf("Expected 1, found %v", argument)
	}
}

func TestStringArgument(t *testing.T) {
	processName, argument := ParseProcessId("P(str)")
	if processName != "P" {
		t.Errorf("Expected P, found %s", processName)
	}
	if argument != "str" {
		t.Errorf("Expected str, found %v", argument)
	}
}
