---- MODULE NoFirstLabel ----
EXTENDS Sequences, FiniteSets, Integers
(*
--mpcal NoFirstLabel {
    procedure MPCalProc(a) {
        \*:: expectedError: LabelRequiredError
        print(2 + 2);
    }
    archetype MyArchetype() {
        (*:: expectedError: LabelRequiredError *)
        print(1 + 1);
    }
    procedure PCalProc(a) {
        \*:: expectedError: LabelRequiredError
        print(3 + 3);
    }

    process (Proc = 1) {
        \*:: expectedError: LabelRequiredError
        print(4 + 4);
    }
}
*)
\* BEGIN TRANSLATION
====