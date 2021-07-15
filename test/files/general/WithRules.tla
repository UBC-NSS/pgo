---- MODULE WithRules ----
EXTENDS Sequences, FiniteSets, Integers
(*
--mpcal WithRules {
     macro MacroWith() {
         print(1 + 1);
         with (x = 10) {
             print x;
             \*:: expectedError: LabelForbiddenError
             m1: x := 20; (* invalid *)
         };
         \*:: expectedError: LabelForbiddenError
         m2: print(20); (* invalid *)
     }

     procedure ProcedureWith() {
         l1: with (x = 10) {
                 \*:: expectedError: LabelForbiddenError
                 l2: print x; (* invalid *)
             }
     }
}
*)
\* BEGIN TRANSLATION
====