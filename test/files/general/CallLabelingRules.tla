---- MODULE CallLabelingRules ----
EXTENDS Sequences, FiniteSets, Integers
(*
--mpcal CallLabelingRules {
    procedure SomeProcedure() {
        l99: skip;
    }

    procedure MyProcedure() {
        l2: print "procedure";
        call SomeProcedure();
        return; (* no label required *)
    }

    archetype MyArchetype() {
        l1: print "first label";
        call MyProcedure();
        \*:: expectedError: LabelRequiredError
        call MyProcedure();
    }

    process (MyProcess = 32)
    variables x;
    {
        l3: print "process";
        call MyProcedure();
        goto l3; (* no label required *)
        l4: print "next label";
        call MyProcedure();
        \*:: expectedError: LabelRequiredError
        x := 10; (* missing label *)
    }
}
*)
\* BEGIN TRANSLATION
====