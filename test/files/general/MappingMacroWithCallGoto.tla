---- MODULE MappingMacroWithCallGoto ----
EXTENDS Sequences, FiniteSets, Integers
(*
--mpcal MappingMacroWithCallGoto {
    procedure YesProcedure() {
        l1: skip;
    }
    procedure NoProcedure() {
        l2: skip;
    }

     mapping macro InvalidStatements {
         read {
          await Len($variable) = 0;
          if (TRUE) {
              call YesProcedure();
          };
          \*:: expectedError: LabelRequiredError
          call NoProcedure();
          \*:: expectedError: LabelRequiredError
          yield 0;
      }
      write {
          either { yield $value }
          or     { (*:: expectedError: LabelForbiddenError *) l1: goto l1 };
      }
     }
}
*)
\* BEGIN TRANSLATION
====