-- Tests/Specification.lean
import Grounding
import Modality
import Situation
import Spec.Check

-- Every axiom of the development is a field of `Spec.Theory`, filled
-- by itself in `developmentTheory`, and no source file is left out.
#check_axioms_are_fields
