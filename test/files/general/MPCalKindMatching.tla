---- MODULE MPCalKindMatching ----
EXTENDS Sequences, FiniteSets, Integers
(*
--mpcal MPCalKindMatching {
    procedure Proc(ref a[_])
        variables x;
    {
        l2: call Proc((*:: expectedError: MPCalKindMismatchError *) a);
        l4: call Proc2(ref a[_][_]);
        l5: a[2] := 3;
        l3: (*:: expectedError: MPCalKindMismatchError *) a := 3;
        l6: a[5][6] := 3;
        l7: x := (*:: expectedError: MPCalKindMismatchError *) a;
        l8: x := a[3];
        l9: x := a[(*:: expectedError: MPCalKindMismatchError *) a];
        l10: x := a[3][4];
        l11: call Proc((*:: expectedError: MPCalKindMismatchError *) ref a);
        l12: call Proc(ref a[_]);
        l13: call Proc((*:: expectedError: MPCalKindMismatchError *) ref a[_][_]);
    }

    procedure Proc2(ref b[_][_]) {
        l3: skip;
    }

    archetype Arch(ref a[_]) {
        l1: skip;
    }

    variables myVar;

    process (A = 42) == instance Arch(ref myVar[_]);

    process (B = 43) == instance Arch((*:: expectedError: MPCalKindMismatchError *) ref myVar);

    process (C = 44) == instance Arch(myVar); \* will generate a synthetic local var

    process (D = 45) == instance Arch((*:: expectedError: MPCalKindMismatchError *) ref myVar[_][_]);
}
*)
\* BEGIN TRANSLATION
====