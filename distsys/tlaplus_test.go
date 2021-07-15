package distsys

import "testing"

func TestTLAModel(t *testing.T) {
	type Record struct {
		Name           string
		Operation      func() TLAValue
		ExpectedResult string
	}

	tests := []Record{
		{
			Name: "Seq({})",
			Operation: func() TLAValue {
				return TLA_Seq(NewTLASet())
			},
			ExpectedResult: "{<<>>}",
		},
		{
			Name: "\\E foo \\in {} : TRUE",
			Operation: func() TLAValue {
				return TLAQuantifiedExistential([]TLAValue{NewTLASet()}, func([]TLAValue) bool {
					return true
				})
			},
			ExpectedResult: "FALSE",
		},
	}

	for _, test := range tests {
		t.Run(test.Name, func(t *testing.T) {
			actualValue := test.Operation()
			actualStr := actualValue.String()
			if actualStr != test.ExpectedResult {
				t.Errorf("result %s did not equal expected value %s", actualStr, test.ExpectedResult)
			}
		})
	}
}
