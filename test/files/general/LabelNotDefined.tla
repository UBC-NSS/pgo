---- MODULE LabelNotDefined ----
EXTENDS Sequences, FiniteSets, Integers
(*
--mpcal LabelNotDefined {
     procedure Proc() {
        l1:
        \*:: expectedError: LabelNotDefinedError
        goto l2;
     }

     process (P = 1) {
        pl1: (*:: expectedError: LabelNotDefinedError *) goto pl2;
     }
     process (P = 2) {
        pl2: (*:: expectedError: LabelNotDefinedError *) goto pl1;
     }
}
*)
\* BEGIN TRANSLATION
====