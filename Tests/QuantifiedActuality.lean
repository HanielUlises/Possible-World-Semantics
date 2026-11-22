-- Tests/QuantifiedActuality.lean
import Modality.QuantifiedActuality

open QuantifiedActuality Formula

-- "Everything actually exists" is real-world valid over universal
-- models, but its necessitation is not.
example : RWValid (UniversalModels (π := Nat)) allActual ∧
    ¬ RWValid (UniversalModels (π := Nat)) (box allActual) :=
  quantified_contingent_logical_truth

-- "Everything exists" is generally valid, so necessary.
example : GValid (AllModels (π := Nat)) (box allExist) :=
  allExist_gValid.nec

-- Commuting 𝒜 with ∀ is real-world valid, generally valid over
-- constant domains, and not generally valid with a growing domain.
example (φ : Formula Nat) :
    RWValid AllModels (commute 0 φ) ∧ GValid ConstantDomain (commute 0 φ) :=
  ⟨commute_rwValid _ 0 φ, commute_gValid_constant 0 φ⟩

example : ¬ GValid (UniversalModels (π := Nat)) (commute 0 (E 0)) :=
  commute_not_gValid growing_universal

-- The propositional characterization carries over under every
-- assignment.
example (M : Model Nat) (φ : Formula Nat) (w : M.W) (g : Nat → M.D) :
    sat M (box (iff φ (act φ))) w g ↔
      ∀ v, M.R w v → (sat M φ v g ↔ sat M φ M.actual g) :=
  sat_box_actuality M φ w g

-- Nothing here rests on an axiom of the development.
#print axioms quantified_contingent_logical_truth
#print axioms commute_gValid_constant
