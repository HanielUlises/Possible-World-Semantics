import Situation.Definitions
import Situation.Theorems
import Situation.Infimum

/-
  VARIANT AXIOMATIZATIONS

  Two variants of the theory that differ from it in how truth is
  treated.  Each variant's extra assumption is taken as a hypothesis,
  so no axiom is added.

  * If truth in a situation is classical at every object, then any two
    objects make the same propositions true, and there is at most one
    situation (`classical_truth_collapse`,
    `classical_truth_one_situation`).
  * If worldhood is defined with a tautology in place of obtaining,
    then the actual world's being a world, together with classical
    negation at the actual world, leaves no propositions
    (`tautological_worldhood_empty`).
-/

/-- If negation is classical for truth in every object, any two
    objects make the same propositions true. -/
theorem classical_truth_collapse
    (hneg : ∀ (s : World) (p : Propn), (s ⊨ ¬ₚ p) ↔ ¬ (s ⊨ p))
    (s s' : World) (p : Propn) : (s ⊨ p) ↔ (s' ⊨ p) := by
  have h : ¬ ((s ⊨ p) ∧ (s' ⊨ p)) ↔ (¬ (s ⊨ p) ∧ ¬ (s' ⊨ p)) := by
    rw [← TrueIn_meet, ← hneg, TrueIn_meet, hneg, hneg]
  constructor
  · intro hs
    exact Classical.byContradiction fun hs' => (h.mp fun hc => hs' hc.2).1 hs
  · intro hs'
    exact Classical.byContradiction fun hs => (h.mp fun hc => hs hc.1).2 hs'

/-- If negation is classical for truth in every object, there is at
    most one situation. -/
theorem classical_truth_one_situation
    (hneg : ∀ (s : World) (p : Propn), (s ⊨ ¬ₚ p) ↔ ¬ (s ⊨ p))
    (s s' : World) (hs : Situation s) (hs' : Situation s') : s = s' :=
  situation_extensionality_via_truth s s' hs hs' (classical_truth_collapse hneg s s')

/-- Worldhood with a tautology in place of obtaining. -/
def TautologicalWorldhood (s : World) : Prop :=
  Situation s ∧ ◊ (fun _ => ∀ p : Propn, (s ⊨ p) ↔ True) actualWorld

/-- If the actual world is a world in the tautological sense and
    negation is classical at it, there are no propositions. -/
theorem tautological_worldhood_empty
    (hw : TautologicalWorldhood actualWorld)
    (hneg : ∀ p : Propn, (actualWorld ⊨ ¬ₚ p) ↔ ¬ (actualWorld ⊨ p))
    (p : Propn) : False := by
  obtain ⟨_, _, hall⟩ := (Diamond_iff_exists _ _).mp hw.2
  exact (hneg p).mp ((hall (¬ₚ p)).mpr trivial) ((hall p).mpr trivial)
