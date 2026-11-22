import Grounding.Ontology
import Grounding.Truth
import Grounding.Parthood
import Situation.Definitions
import Situation.Theorems

/-
  INFIMUM (MEET) OF SITUATIONS

  The meet of two situations is the largest situation
  that is a part of both.  It is defined, as in Zalta's theory, by
  comprehension: the meet of s and s' is the abstract object that
  encodes exactly the properties encoded by both.  Its truth
  conditions and its situationhood, formerly postulated, are
  theorems.

  This is the situation-semantic analogue of set-theoretic
  intersection restricted to the situational domain.
-/

/--
  The meet of s and s': the abstract object that encodes exactly the
  properties encoded by both s and s'.  It exists by `Comprehension`
  and is unique by `abstract_extensionality`.
-/
noncomputable def meet (s s' : World) : World :=
  Classical.choose (Comprehension (fun F => Enc s F ∧ Enc s' F))

/-- The defining property of the meet. -/
theorem meet_spec (s s' : World) :
    A! (meet s s') ∧ ∀ F : Property, Enc (meet s s') F ↔ (Enc s F ∧ Enc s' F) :=
  Classical.choose_spec (Comprehension (fun F => Enc s F ∧ Enc s' F))

/--
  The meet is itself a situation when its components are.
  Formerly postulated.
-/
theorem meet_situation : ∀ s s' : World,
    Situation s → Situation s' → Situation (meet s s') :=
  fun s s' hs _ => ⟨(meet_spec s s').1, fun F hF => hs.2 F (((meet_spec s s').2 F).mp hF).1⟩

/--
  The meet makes precisely the shared truths true.
  Formerly postulated.
-/
theorem TrueIn_meet :
    ∀ (s s' : World) (p : Propn),
      (meet s s' ⊨ p) ↔ ((s ⊨ p) ∧ (s' ⊨ p)) := by
  intro s s' p
  rw [TrueIn_iff_Enc _ (object_total _), (meet_spec s s').2,
    TrueIn_iff_Enc _ (object_total _), TrueIn_iff_Enc _ (object_total _)]

/-- The meet is a part of its left argument.
    Every proposition true at the meet is true at the left component
    by definition of TrueIn_meet; truth_mono_to_part converts this
    truth-inclusion into the required parthood. -/
theorem meet_le_left :
    ∀ (s s' : World),
      Situation s → Situation s' → (meet s s' ⊴ s) := by
  intro s s' hs hs'
  exact truth_mono_to_part (meet s s') s
    (meet_situation s s' hs hs') hs
    (fun p h => ((TrueIn_meet s s' p).mp h).1)

/-- The meet is a part of its right argument.
    Symmetric to meet_le_left: take the right conjunct from TrueIn_meet. -/
theorem meet_le_right :
    ∀ (s s' : World),
      Situation s → Situation s' → (meet s s' ⊴ s') := by
  intro s s' hs hs'
  exact truth_mono_to_part (meet s s') s'
    (meet_situation s s' hs hs') hs'
    (fun p h => ((TrueIn_meet s s' p).mp h).2)

/-- Any common lower bound is a part of the meet.
    If x is a part of both s and s', then every proposition true at x
    is true at s (via part_truth_mono) and at s' (likewise), so true at
    the meet by TrueIn_meet; truth_mono_to_part closes the parthood. -/
theorem meet_greatest :
    ∀ (x s s' : World),
      Situation x → Situation s → Situation s' →
      (x ⊴ s) → (x ⊴ s') → (x ⊴ meet s s') := by
  intro x s s' hx hs hs' hxs hxs'
  exact truth_mono_to_part x (meet s s') hx
    (meet_situation s s' hs hs')
    (fun p hxp =>
      (TrueIn_meet s s' p).mpr
        ⟨part_truth_mono x s hx hs hxs p hxp,
         part_truth_mono x s' hx hs' hxs' p hxp⟩)

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
