---- MODULE IfEitherLabelingRules ----
EXTENDS Sequences, FiniteSets, Integers
(*
--mpcal IfEitherLabelingRules {

  procedure MyProcedure()
  variables v;
  {
         l2: print "procedure";
         either { v := 10 } or { return };
         \*:: expectedError: LabelRequiredError
         goto l2; (* missing label *)
     }

  archetype MyArchetype() {
         l1: print "first label";
         if (TRUE) {
             print "true";
         } else if (TRUE) {
             call MyProcedure();
         };

         \*:: expectedError: LabelRequiredError
         print "needs label"; (* missing label *)
     }

  process (MyProcess = 32)
  variables x, y;
  {
         l3: print "process";
         either { x := 0 } or { goto l3 };
         l4: print "all good";

         either { goto l4 } or { skip };
         \*:: expectedError: LabelRequiredError
         x := 50; (* missing label *)

         l5: if (TRUE) {
                 l6: print "label";
             };
         \*:: expectedError: LabelRequiredError
         y := 20; (* missing label *)

         l6: while(TRUE) {
            l7: skip;
         };
         skip; \* ok, no label needed (this says something about the correct desugaring for while)
     }
}
*)
\* BEGIN TRANSLATION
====