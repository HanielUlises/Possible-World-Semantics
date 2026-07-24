-- Test/Smoke.lean
import Grounding.Ontology
import Grounding.Parthood
import Grounding.Dependence
import Grounding.AbstractObjects
import Modality.Operators
import Situation.Definitions
import Situation.Theorems

/-
  Smoke tests: verify that the axiom inventory is not
  trivially inconsistent by constructing explicit witnesses.
-/

-- partOf_refl compiles: reflexivity holds for any world
#check @partOf_refl

-- partOf_trans compiles: transitivity holds
#check @partOf_trans

-- The definitions are well-typed
#check @Maximal₁
#check @Consistent
#check @Actual
#check @Worldhood

-- Maximal₁ and Partial₁ are mutually exclusive
#check @maximal₁_not_partial₁

-- Worlds are maximal₁
#check @world_maximal

-- The actual world is a world
#check @actualWorld_is_world

-- Derived theory (added extensions) elaborates
#check @Diamond_distrib_disj
#check @Box_distrib_conj
#check @abstract_object_unique
#check @not_foundational_iff_derivative
#check @persistent_disj
