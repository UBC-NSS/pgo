---- MODULE RecursiveMacroRules ----
EXTENDS Sequences, FiniteSets, Integers
(*
--mpcal RecursiveMacroRules {
     macro RecursiveMacro(x) {
        \*:: expectedError: RecursiveMacroError
        RecursiveMacro(x)
     }

     macro Indirect1(x) {
        \*:: expectedError: RecursiveMacroError
        Indirect2(x)
     }
     macro Indirect2(x) {
        \*:: expectedError: RecursiveMacroError
        Indirect1(x)
     }

     procedure CallsMacro() {
        label:
            \*:: expectedError: RecursiveMacroError
            Indirect1(5)
     }
}
*)
\* BEGIN TRANSLATION
====