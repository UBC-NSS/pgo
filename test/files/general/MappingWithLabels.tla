---- MODULE MappingWithLabels ----
EXTENDS Sequences, FiniteSets, Integers
(*
--mpcal MappingWithLabels {
     mapping macro ContainsLabels {
      read {
          \*:: expectedError: LabelForbiddenError
          r: yield $variable
      }
      write {
          if ($variable > 10) {
              \*:: expectedError: LabelForbiddenError
              w: yield $value;
          }
      }
     }
}
*)
\* BEGIN TRANSLATION
====