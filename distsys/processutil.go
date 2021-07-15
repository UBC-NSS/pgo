package distsys

import (
	"strings"
)

func ParseProcessId(processId string) (string, string) {
	leftParens := strings.Index(processId, "(")
	if leftParens < 0 {
		panic("Missing left parenthesis for process ID " + processId)
	}
	processName := processId[:leftParens]
	if processName == "" {
		panic("Missing process name for process ID " + processId)
	}
	rightParens := strings.LastIndex(processId, ")")
	if rightParens < 0 {
		panic("Missing right parenthesis for process ID " + processId)
	}
	argument := processId[leftParens+1 : rightParens]
	if argument == "" {
		panic("Missing processs argument for process ID " + processId)
	}
	return processName, argument
}
