---- MODULE MacroRules ----
EXTENDS Sequences, FiniteSets, Integers
(*
--mpcal MacroRules {
     macro ValidMacro() {
         print(1 + 1);
         x := 10;
     }

     macro InvalidMacro() {
         either { skip } or { (*:: expectedError: LabelForbiddenError *) l1: print(10) }; (* invalid *)
         \*:: expectedError: LabelForbiddenError
         l2: print(20); (* invalid *)
     }
}
*)
\* BEGIN TRANSLATION
====