|---- MODULE WhileLabels ----
EXTENDS Sequences, FiniteSets, Integers
(*
--mpcal WhileLabels {
    procedure CorrectProcedure() {
        l2: print "procedure";
        l3: while (FALSE) { print(3 - 3) }; (* all good *)
    }

    archetype IncorrectArchetype() {
        l1: print "first label";
        \*:: expectedError: LabelRequiredError
        while (TRUE) { print "hello" };
    }

    process (IncorrectProcess = 32) {
        \*:: expectedError: LabelRequiredError
        while (10 < 20) { print(2 * 2) };
    }

    process (NestedMissingWhileLabels = 33) {
        \*:: expectedError: LabelRequiredError
        while (10 < 20) {
            \*:: expectedError: LabelRequiredError
            while(20 < 30) { print(3 * 3) };
        };
    }
}
*)
\* BEGIN TRANSLATION
====