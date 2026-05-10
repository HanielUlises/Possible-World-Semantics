import Grounding.Ontology
import Grounding.Truth
import Grounding.Parthood
import Situation.Definitions
import Situation.Theorems

/-
  INFIMUM (MEET) OF SITUATIONS

  The meet of two situations is the largest situation
  that is a part of both.  Since situations are individuated
  by their propositional content (via extensionality), the
  meet is characterised by the propositions true in both.

  This is the situation-semantic analogue of set-theoretic
  intersection restricted to the situational domain.
-/

/--
  The meet of s and s' is a world that makes exactly the
  propositions true that are true in both s and s'.

  Its existence is not derivable from the primitives alone
  and is therefore postulated.
-/
axiom meet : World → World → World

/--
  The meet is itself a situation when its components are.
-/
axiom meet_situation : ∀ s s' : World,
    Situation s → Situation s' → Situation (meet s s')

/--
  The meet makes precisely the shared truths true.
-/
axiom TrueIn_meet :
  ∀ (s s' : World) (p : Propn),
    (meet s s' ⊨ p) ↔ ((s ⊨ p) ∧ (s' ⊨ p))

/-
  Open proof obligation OP-4: lattice structure of meet.

  meet_le_left, meet_le_right, and meet_greatest all require
  connecting TrueIn_meet (which governs truth) to PartOf
  (which is defined over Enc). This bridge does not exist
  without truth_mono_to_part (OP-2).

  Specifically:
    meet_le_left  needs: (meet s s' ⊨ p → s ⊨ p) → meet s s' ⊴ s
    meet_le_right needs: (meet s s' ⊨ p → s' ⊨ p) → meet s s' ⊴ s'
    meet_greatest needs: (x ⊨ p → meet s s' ⊨ p) → x ⊴ meet s s'

  All three reduce to truth_mono_to_part.
  See README.md § Open Proof Obligations, OP-4.
-/

/-- The meet is a part of its left argument.
    Blocked by OP-4 (requires OP-2). -/
theorem meet_le_left :
    ∀ (s s' : World), (meet s s' ⊴ s) := by
  intro s s'
  sorry -- OP-4: requires truth_mono_to_part

/-- The meet is a part of its right argument.
    Blocked by OP-4 (requires OP-2). -/
theorem meet_le_right :
    ∀ (s s' : World), (meet s s' ⊴ s') := by
  intro s s'
  sorry -- OP-4: requires truth_mono_to_part

/-- Any common lower bound is a part of the meet.
    Blocked by OP-4 (requires OP-2). -/
theorem meet_greatest :
    ∀ (x s s' : World),
      (x ⊴ s) → (x ⊴ s') → (x ⊴ meet s s') := by
  intro x s s' _hxs _hxs'
  sorry -- OP-4: requires truth_mono_to_part

/-- The meet of a situation with itself is itself. -/
theorem meet_self :
    ∀ s : World,
      Situation s →
      meet s s = s := by
  intro s hs
  apply situation_extensionality_via_truth (meet s s) s (meet_situation s s hs hs) hs
  intro p
  constructor
  · intro h
    exact ((TrueIn_meet s s p).mp h).1
  · intro h
    exact (TrueIn_meet s s p).mpr ⟨h, h⟩


/-- The meet is commutative up to situational identity. -/
theorem meet_comm :
    ∀ s s' : World,
      Situation s → Situation s' →
      meet s s' = meet s' s := by
  intro s s' hs hs'
  apply situation_extensionality_via_truth
    (meet s s') (meet s' s)
    (meet_situation s s' hs hs')
    (meet_situation s' s hs' hs)
  intro p
  simp only [TrueIn_meet]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
