-- Tests/Model.lean
import Model.Satisfiable
import Spec.Check

-- The model is an instance of `Spec.Theory`, built using only Lean's own
-- logic: the axioms of the development are consistent.
#check_only_core_axioms Model.theory
#check_only_core_axioms Model.nondegenerate
#check_only_core_axioms Model.quantified_contingent_logical_truth
