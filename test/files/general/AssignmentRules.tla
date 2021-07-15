---- MODULE AssignmentRules ----
EXTENDS Sequences, FiniteSets, Integers
(*
--mpcal AssignmentRules {
  macro MyMacro(x) {
    x := 3;
    \*:: expectedError: MultipleAssignmentError
    y := 4;
  }

  procedure Proc2()
  variables x, y;
  {
        l1: MyMacro(x);
        l2: MyMacro(x); MyMacro( (*:: expectedError: MultipleAssignmentError *) x);
        l3: MyMacro(x); (*:: expectedError: MultipleAssignmentError *) y := y + 1;
        l4: MyMacro(x); (*:: expectedError: MultipleAssignmentError *) x := -1;
  }

  procedure MyProcedure(x, y)
  variables x, y;
  {
         p: either { y := 10 } or { skip };
            \*:: expectedError: MultipleAssignmentError
            y := 11; (* missing label *)
         p2: y := 20;
             x := y || (*:: expectedError: MultipleAssignmentError *) y := x; (* swap x and y: invalid *)
     }

  archetype MyArchetype(ref x)
  variables x;
  {
         a1: x := 10;
         \*:: expectedError: MultipleAssignmentError
         x := 11; (* missing label *)
     }

  process (MyProcess = 23)
  variables n;
  {
         l1: n := 2;
         l2: while (n < 10) {
             n := 12;
             if (n = 20) {
                 \*:: expectedError: MultipleAssignmentError
                 n := 100; (* missing label *)
             }
         };
         \*:: expectedError: MultipleAssignmentError
         n := 32; (* label not missing *)

         l3: if (n = 32) {
             n := 0;
         };
         \*:: expectedError: MultipleAssignmentError
         n := 12; (* missing label *)
     }
}
*)
\* BEGIN TRANSLATION
====