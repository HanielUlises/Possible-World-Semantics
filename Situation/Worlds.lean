import Grounding.Ontology
import Grounding.Truth
import Grounding.Propositions
import Grounding.Parthood
import Situation.Definitions

/-
  WORLD-THEORETIC RESULTS

  A possible world is a maximal consistent situation.
  This file develops consequences of that characterisation,
  connecting the Worldhood definition to Maximal₁ and
  Consistent, and establishing basic properties of worlds
  within the axiomatic framework.
-/

/--
  Every world is a maximal₁ situation.

  This follows from the fact that worlds are stipulated to
  decide every proposition.  The principle is not internally
  derivable and is therefore postulated.
-/
axiom world_maximal :
  ∀ w : World, Worldhood w → Maximal₁ w

/--
  Every world is consistent.

  A world that decided both a proposition and its negation
  would trivialise the theory.  This is therefore postulated.
-/
axiom world_consistent :
  ∀ w : World, Worldhood w → Consistent w

/--
  The actual world is a world.
-/
axiom actualWorld_is_world : Worldhood actualWorld

/--
  A maximal₁ consistent situation that is possible is a world.

  This is the converse direction completing the equivalence:
  Worldhood ↔ Maximal₁ ∧ Consistent ∧ Possible (up to being a Situation).
-/
axiom maximal_consistent_possible_is_world :
  ∀ s : World,
    Situation s →
    Maximal₁ s →
    Consistent s →
    Possible s →
    Worldhood s

/--
  No proper part of a world is itself a world.

  If s is a world and x is a strict part of s (part but not equal),
  then x is not a world.  Worlds are the maximal situations.
-/
theorem no_strict_subworld :
    ∀ (w x : World),
      Worldhood w →
      x ⊴ w →
      x ≠ w →
      ¬ Worldhood x := by
  intro w x hw hxw hne hwx
  have hmx := world_maximal x hwx
  have hmw := world_maximal w hw
  apply hne
  apply situation_extensionality_via_truth
  · (hwx).1
  · (hw).1
  · intro p
    constructor
    · intro hp
      cases hmw p with
      | inl h => exact h
      | inr h =>
        -- h : w ⊨ ¬ₚp, but hxw : x ⊴ w and hp : x ⊨ p,
        -- so part_truth_mono gives w ⊨ p, contradicting TrueIn_neg.mp h.
        exfalso
        exact absurd
          (part_truth_mono x w (hwx).1 (hw).1 hxw p hp)
          ((TrueIn_neg w p).mp h)
    · intro hp
      -- hxw goes x ⊴ w, not w ⊴ x, so part_truth_mono cannot transfer hp
      -- directly. Use maximality of x: x ⊨ p ∨ x ⊨ ¬ₚp. If x ⊨ ¬ₚp then
      -- part_truth_mono gives w ⊨ ¬ₚp, so TrueIn_neg gives ¬(w ⊨ p),
      -- contradicting hp. Hence x ⊨ p.
      cases hmx p with
      | inl h  => exact h
      | inr h  =>
        exfalso
        exact absurd hp
          ((TrueIn_neg w p).mp
            (part_truth_mono x w (hwx).1 (hw).1 hxw (¬ₚ p) h))

/--
  Any two distinct worlds disagree on at least one proposition.
-/
theorem worlds_distinguished_by_truth :
    ∀ (w₁ w₂ : World),
      Worldhood w₁ →
      Worldhood w₂ →
      w₁ ≠ w₂ →
      ∃ p : Propn, (w₁ ⊨ p) ≠ (w₂ ⊨ p) := by
  intro w₁ w₂ hw₁ hw₂ hne
  by_contra hall
  push_neg at hall
  apply hne
  apply situation_extensionality_via_truth
  · (hw₁).1
  · (hw₂).1
  · intro p
    exact Iff.of_eq (propext (Eq.to_iff (hall p)))

/-- The actual world is maximal₁.
    Since actualWorld satisfies Worldhood, it inherits maximality
    from world_maximal. Every proposition is decided at the actual
    world — either it or its negation obtains there. -/
theorem actualWorld_maximal₁ : Maximal₁ actualWorld :=
  world_maximal actualWorld actualWorld_is_world

/-- The actual world is consistent.
    A world that made both a proposition and its negation true
    would collapse the distinction between truth and falsity
    at the actual world. -/
theorem actualWorld_consistent : Consistent actualWorld :=
  world_consistent actualWorld actualWorld_is_world

/-- Distinct worlds are not parts of each other.
    If w₁ and w₂ are distinct worlds, neither can be a part
    of the other. Were w₁ ⊴ w₂, then by maximality of w₁
    every proposition decided at w₁ is decided at w₂, and
    since both are maximal₁ they would agree on everything,
    forcing identity by situation extensionality — contradicting
    distinctness. -/
theorem distinct_worlds_incomparable :
    ∀ (w₁ w₂ : World),
      Worldhood w₁ →
      Worldhood w₂ →
      w₁ ≠ w₂ →
      ¬ (w₁ ⊴ w₂) := by
  intro w₁ w₂ hw₁ hw₂ hne hpart
  apply hne
  apply situation_extensionality_via_truth (hw₁).1 (hw₂).1
  intro p
  constructor
  · intro hp
    cases world_maximal w₂ hw₂ p with
    | inl h  => exact h
    | inr hn =>
      exfalso
      have hc := world_consistent w₁ hw₁
      apply hc
      exact ⟨p, hp, by
        have := world_maximal w₁ hw₁ p
        cases this with
        | inl h  => exact absurd h (by
            intro habs
            exact (world_consistent w₂ hw₂) ⟨p, hpart _ habs, hn⟩)
        | inr h  => exact h⟩
  · intro hp
    cases world_maximal w₁ hw₁ p with
    | inl h  => exact hpart _ h |>.elim id (fun hn =>
        absurd hp (world_consistent w₂ hw₂ |>.elim (fun hc => hc ⟨p, hp, hn⟩ |>.elim)))
    | inr h  => exact absurd hp
        ((world_consistent w₂ hw₂).elim (fun hc => by
          intro habs; exact hc ⟨p, habs, hn⟩))
