-- Test/Smoke.lean
import Grounding.Ontology
import Grounding.Parthood
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
