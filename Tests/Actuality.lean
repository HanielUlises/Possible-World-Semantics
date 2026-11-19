-- Tests/Actuality.lean
import Situation.Actuality

open ActualityLogic

-- The actuality truth is real-world valid in S5, but its
-- necessitation is not.
example (a : Nat) :
    RWValid S5Models (Formula.iff (.atom a) (.act (.atom a))) ∧
    ¬ RWValid S5Models (.box (Formula.iff (.atom a) (.act (.atom a)))) :=
  ⟨actuality_rwValid _ _, box_actuality_not_rwValid twoWorlds_S5 a⟩

-- General validity is closed under necessitation.
example (C : ModelClass Nat) (φ : Formula Nat) (h : GValid C φ) :
    GValid C (.box φ) :=
  h.nec

-- In the development, the actuality truth holds at the actual world
-- for every condition, and fails to be necessary for contingent ones.
example (p : World → Prop) : (fun w => p w ↔ 𝒜 p w) actualWorld :=
  actuality_truth p

example (p : World → Prop) (hc : Contingent p actualWorld) :
    ¬ □ (fun v => p v ↔ 𝒜 p v) actualWorld :=
  contingent_actuality_truth_not_necessary p actualWorld hc
