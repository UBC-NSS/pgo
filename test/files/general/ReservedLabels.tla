---- MODULE ReservedLabels ----
EXTENDS Sequences, FiniteSets, Integers
(*
--mpcal ReservedLabels {
     procedure MyProcedure(y) {
         p: either { p1: y := 20 } or { (*:: expectedError: ReservedLabelError *) Error: skip }; (* reserved *)
     }

  archetype MyArchetype(ref x) {
         \*:: expectedError: ReservedLabelError
         Done: x := 10; (* reserved *)
         done: x := 30; (* no problem *)
     }
}
*)
\* BEGIN TRANSLATION
====