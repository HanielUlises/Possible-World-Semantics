import Grounding.Ontology
import Grounding.Propositions
import Grounding.Truth
import Grounding.Parthood
import Situation.Definitions
import Grounding.AbstractObjects

/-
  THEOREMS OF SITUATION SEMANTICS
-/

/--
  Theorem 2 (extensionality of situations via truth).

  Two situations are identical iff they make exactly the
  same propositions true.  This is situation_extensionality
  with its ExtEq hypothesis unfolded.
-/
theorem situation_extensionality_via_truth :
    ∀ s₁ s₂ : World,
      Situation s₁ →
      Situation s₂ →
      (∀ p : Propn, (s₁ ⊨ p) ↔ (s₂ ⊨ p)) →
      s₁ = s₂ :=
  fun s₁ s₂ h₁ h₂ h => situation_extensionality s₁ s₂ ⟨h₁, h₂, h⟩

/-- Maximality₁ excludes partiality₁. -/
theorem maximal₁_not_partial₁ :
    ∀ s : World, Maximal₁ s → ¬ Partial₁ s := by
  intro s hmax hpart
  rcases hpart with ⟨p, hp, hnp⟩
  cases hmax p with
  | inl hp' => exact hp hp'
  | inr hnp' => exact hnp hnp'

/-- Actual situations are possible: the actual index witnesses it. -/
theorem actual_implies_possible :
    ∀ s : World, Actual s → Possible s :=
  fun _ h => (Diamond_iff_exists _ _).mpr ⟨actualIndex, R_refl actualIndex, h⟩

/-- Maximality₂ implies non-partiality₂. -/
theorem maximal₂_not_partial₂ :
    ∀ s : World, Maximal₂ s → ¬ Partial₂ s := by
  intro s hmax hpart
  rcases hpart with ⟨p, hp⟩
  exact hp (hmax p)

/-- Every abstract part of a situation is itself a situation
    (Zalta 1993, Theorem 3, which ranges over abstract objects).
    Without the A! hypothesis every ordinary object, which encodes
    nothing and is therefore a part of everything, would count as a
    situation.  Formerly postulated; it follows from the definition
    of `Situation`, since a part encodes only what the whole does. -/
theorem situation_closed_under_parthood :
    ∀ s x : World, Situation s → A! x → (x ⊴ s) → Situation x :=
  fun _ _ hs hx hxs => ⟨hx, fun F hF => hs.2 F (hxs F hF)⟩

/-- Parthood is monotone with respect to truth.
    If x is a part of y and p is persistent, truth of p
    transfers from x to y. -/
theorem parthood_truth_monotone :
    ∀ (x y : World) (p : Propn),
      Situation x →
      Situation y →
      (x ⊴ y) →
      Persistent p →
      (x ⊨ p) →
      (y ⊨ p) := by
  intro x y p hx hy hxy hpers hxp
  exact hpers x y hx hy hxp hxy

/-- Persistent propositions are closed upward along parthood. -/
theorem persistent_upward_closed :
    ∀ p : Propn,
      Persistent p ↔
      ∀ x y : World, Situation x → Situation y →
        (x ⊴ y) → (x ⊨ p) → (y ⊨ p) := by
  intro p
  constructor
  · intro h x y hx hy hxy hxp
    exact h x y hx hy hxp hxy
  · intro h x y hx hy hxp hxy
    exact h x y hx hy hxy hxp

/-- The conjunction of two persistent propositions is persistent. -/
theorem persistent_conj :
    ∀ p q : Propn,
      Persistent p →
      Persistent q →
      Persistent (p ∧ₚ q) := by
  intro p q _ _ s s' hs hs' hpq hss'
  exact part_truth_mono s s' hs hs' hss' (p ∧ₚ q) hpq

/-- The disjunction of two persistent propositions is persistent.
    Like every proposition, it is carried upward along parthood by
    part_truth_mono. -/
theorem persistent_disj :
    ∀ p q : Propn,
      Persistent p →
      Persistent q →
      Persistent (p ∨ₚ q) := by
  intro p q _ _ s s' hs hs' hpq hss'
  exact part_truth_mono s s' hs hs' hss' (p ∨ₚ q) hpq

/-- Consistency is downward closed under parthood among situations:
    whatever a part makes true, the whole makes true. -/
theorem consistent_downward_closed :
    ∀ (s x : World), Situation s → Situation x →
      Consistent s → (x ⊴ s) → Consistent x :=
  fun s x hs hx hcon hxs ⟨p, hp, hnp⟩ =>
    hcon ⟨p, part_truth_mono x s hx hs hxs p hp,
             part_truth_mono x s hx hs hxs (¬ₚ p) hnp⟩

/-- Actual situations are consistent: a proposition and its negation
    cannot both obtain at the actual index. -/
theorem actual_consistent :
    ∀ s : World, Actual s → Consistent s :=
  fun _ h ⟨p, hp, hnp⟩ =>
    (Obtains_neg actualIndex p).mp (h (¬ₚ p) hnp) (h p hp)

/-- Partial₂ and Maximal₁ are jointly satisfiable. -/
theorem partial₂_compatible_with_maximal₁ :
    ∀ s : World,
      Maximal₁ s →
      Partial₂ s →
      ∃ p : Propn, ¬ (s ⊨ p) ∧ (s ⊨ ¬ₚ p) := by
  intro s hmax hpart
  rcases hpart with ⟨p, hnp⟩
  cases hmax p with
  | inl hp    => exact absurd hp hnp
  | inr hnegp => exact ⟨p, hnp, hnegp⟩

/-- Theorem 8 (Zalta 1993): every proposition is persistent.
    Follows directly from part_truth_mono once OP-2 and OP-3
    are resolved. -/
theorem all_propositions_persistent :
    ∀ p : Propn, Persistent p := by
  intro p s s' hs hs' hsp hss'
  exact part_truth_mono s s' hs hs' hss' p hsp
