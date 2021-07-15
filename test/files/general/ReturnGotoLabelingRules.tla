---- MODULE ReturnGotoLabelingRules ----
EXTENDS Sequences, FiniteSets, Integers
(*
--mpcal ReturnGotoLabelingRules {

	 procedure MyProcedure() {
		 l2: print "procedure";
		 return;
		 \*:: expectedError: LabelRequiredError
		 goto l2; (* missing label *)
	 }

  archetype MyArchetype() {
		 l1: print "first label";
		 goto l1;
		 \*:: expectedError: LabelRequiredError
		 print "needs label"; (* missing label *)
	 }

	 process (MyProcess = 32)
  variables x;
  {
		 l3: print "process";
		 goto l3;
		 \*:: expectedError: LabelRequiredError
		 x := 10; (* missing label *)
	 }
}
*)
\* BEGIN TRANSLATION
====