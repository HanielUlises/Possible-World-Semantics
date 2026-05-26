import Grounding.Ontology
import Grounding.Propositions
import Grounding.Truth
import Grounding.Parthood
import Situation.Definitions

/-
  THEOREMS OF SITUATION SEMANTICS
-/

/--
  Theorem 2 (extensionality of situations via truth).

  Two situations are identical iff they make exactly the
  same propositions true.
-/
axiom situation_extensionality_via_truth :
  ∀ s₁ s₂ : World,
    Situation s₁ →
    Situation s₂ →
    (∀ p : Propn, (s₁ ⊨ p) ↔ (s₂ ⊨ p)) →
    s₁ = s₂

/--
  Maximality₁ excludes partiality₁.
-/
theorem maximal₁_not_partial₁ :
    ∀ s : World,
      Maximal₁ s →
      ¬ Partial₁ s := by
  intro s hmax hpart
  rcases hpart with ⟨p, hp, hnp⟩
  cases hmax p with
  | inl hp' => exact hp hp'
  | inr hnp' => exact hnp hnp'

/--
  Actual situations are possible.
-/
axiom actual_implies_possible :
  ∀ s : World,
    Actual s →
    Possible s

/--
  Maximality₂ implies non-partiality₂.
-/
theorem maximal₂_not_partial₂ :
    ∀ s : World,
      Maximal₂ s →
      ¬ Partial₂ s := by
  intro s hmax hpart
  rcases hpart with ⟨p, hp⟩
  exact hp (hmax p)

/--
  Every part of a situation is itself a situation.
-/
axiom situation_closed_under_parthood :
  ∀ s x : World,
    Situation s →
    (x ⊴ s) →
    Situation x

/--
  Parthood is monotone with respect to truth.

  If x is a part of y, and p is persistent, then
  truth of p transfers from x to y.
-/
theorem parthood_truth_monotone :
    ∀ (x y : World) (p : Propn),
      (x ⊴ y) →
      Persistent p →
      (x ⊨ p) →
      (y ⊨ p) := by
  intro x y p hxy hpers hxp
  exact hpers x y hxp hxy

/--
  Persistent propositions are closed upward along parthood.
-/
theorem persistent_upward_closed :
    ∀ p : Propn,
      Persistent p ↔
      ∀ x y : World, (x ⊴ y) → (x ⊨ p) → (y ⊨ p) := by
  intro p
  constructor
  · intro h x y hxy hx
    exact h x y hx hxy
  · intro h x y hx hxy
    exact h x y hxy hx

/--
  The conjunction of two persistent propositions is persistent.
-/
theorem persistent_conj :
    ∀ p q : Propn,
      Persistent p →
      Persistent q →
      Persistent (p ∧ₚ q) := by
  intro p q hp hq s s' hpq hss'
  rw [TrueIn_conj] at hpq ⊢
  exact ⟨hp s s' hpq.1 hss', hq s s' hpq.2 hss'⟩

/--
  Consistency is downward closed under parthood.
-/
axiom consistent_downward_closed :
  ∀ (s x : World),
    Consistent s →
    (x ⊴ s) →
    Consistent x

/--
  Actual situations are consistent.
-/
axiom actual_consistent :
  ∀ s : World, Actual s → Consistent s

/--
  Partial₂ and Maximal₁ are jointly satisfiable.
-/
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
    Blocked by OP-2 and OP-3.
    See README.md § Open Proof Obligations. -/
theorem all_propositions_persistent :
    ∀ p : Propn, Persistent p := by
  intro p s s' hsp hss'
  sorry -- OP-2, OP-3

theorem all_propositions_persistent :
    ∀ p : Propn, Persistent p := by
  intro p s s' hsp hss'
  have hss : Situation s := situation_closed_under_parthood s' s
    (by sorry) hss' -- >:(
  exact part_truth_mono s s' hss
    (situation_closed_under_parthood s' s (by sorry) hss')
    hss' p hsp
