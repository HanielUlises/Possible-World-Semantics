import Grounding.Ontology
import Grounding.Truth
import Grounding.Propositions
import Grounding.Parthood
import Situation.Definitions
import Situation.Theorems

/-
  WORLD-THEORETIC RESULTS

  A possible world is a situation whose truths could coincide with
  what obtains (`Worldhood`).  This file derives the classical
  behaviour of truth at worlds, maximality and consistency of worlds,
  and the converse characterisation of worlds as maximal possible
  situations.  All of these were previously postulated; the only
  remaining postulate here concerns the designated actual world.
-/

/--
  A world matches an index: its truths are exactly what obtains there.
-/
theorem world_index (w : World) (hw : Worldhood w) :
    ∃ v : World, ∀ p : Propn, (w ⊨ p) ↔ Obtains v p := by
  obtain ⟨v, _, hv⟩ := (Diamond_iff_exists _ _).mp hw.2
  exact ⟨v, hv⟩

/-- Negation is classical at a world. -/
theorem world_TrueIn_neg (w : World) (hw : Worldhood w) (p : Propn) :
    (w ⊨ ¬ₚ p) ↔ ¬ (w ⊨ p) := by
  obtain ⟨v, hv⟩ := world_index w hw
  rw [hv, hv, Obtains_neg]

/-- Conjunction is classical at a world. -/
theorem world_TrueIn_conj (w : World) (hw : Worldhood w) (p q : Propn) :
    (w ⊨ p ∧ₚ q) ↔ (w ⊨ p) ∧ (w ⊨ q) := by
  obtain ⟨v, hv⟩ := world_index w hw
  rw [hv, hv, hv, Obtains_conj]

/-- Disjunction is classical at a world. -/
theorem world_TrueIn_disj (w : World) (hw : Worldhood w) (p q : Propn) :
    (w ⊨ p ∨ₚ q) ↔ (w ⊨ p) ∨ (w ⊨ q) := by
  obtain ⟨v, hv⟩ := world_index w hw
  rw [hv, hv, hv, Obtains_disj]

/-- Implication is material at a world. -/
theorem world_TrueIn_impl (w : World) (hw : Worldhood w) (p q : Propn) :
    (w ⊨ p →ₚ q) ↔ ((w ⊨ p) → (w ⊨ q)) := by
  obtain ⟨v, hv⟩ := world_index w hw
  rw [hv, hv, hv, Obtains_impl]

/-- Every world is maximal₁: it decides every proposition. -/
theorem world_maximal (w : World) (hw : Worldhood w) : Maximal₁ w :=
  fun p => (Classical.em (w ⊨ p)).imp id (world_TrueIn_neg w hw p).mpr

/-- Every world is consistent. -/
theorem world_consistent (w : World) (hw : Worldhood w) : Consistent w :=
  fun ⟨p, hp, hnp⟩ => (world_TrueIn_neg w hw p).mp hnp hp

/-- Every world is possible. -/
theorem world_possible (w : World) (hw : Worldhood w) : Possible w := by
  obtain ⟨v, hrv, hv⟩ := (Diamond_iff_exists _ _).mp hw.2
  exact (Diamond_iff_exists _ _).mpr ⟨v, hrv, fun p => (hv p).mp⟩

/-- Possible situations are consistent: what could be actual cannot
    contain a proposition together with its negation. -/
theorem possible_consistent (s : World) (hs : Possible s) : Consistent s := by
  obtain ⟨v, _, hv⟩ := (Diamond_iff_exists _ _).mp hs
  exact fun ⟨p, hp, hnp⟩ => (Obtains_neg v p).mp (hv (¬ₚ p) hnp) (hv p hp)

/--
  A maximal₁ possible situation is a world.

  Consistency need not be assumed: it follows from possibility.
-/
theorem maximal_possible_is_world (s : World)
    (hs : Situation s) (hmax : Maximal₁ s) (hpos : Possible s) :
    Worldhood s := by
  obtain ⟨v, hrv, hv⟩ := (Diamond_iff_exists _ _).mp hpos
  refine ⟨hs, (Diamond_iff_exists _ _).mpr ⟨v, hrv, fun p => ⟨hv p, fun hop => ?_⟩⟩⟩
  cases hmax p with
  | inl h => exact h
  | inr h => exact absurd hop ((Obtains_neg v p).mp (hv (¬ₚ p) h))

/-- A maximal₁ consistent situation that is possible is a world. -/
theorem maximal_consistent_possible_is_world (s : World)
    (hs : Situation s) (hmax : Maximal₁ s) (_ : Consistent s)
    (hpos : Possible s) : Worldhood s :=
  maximal_possible_is_world s hs hmax hpos

/-- Worlds are exactly the maximal₁ possible situations. -/
theorem worldhood_iff (s : World) :
    Worldhood s ↔ Situation s ∧ Maximal₁ s ∧ Possible s :=
  ⟨fun hw => ⟨hw.1, world_maximal s hw, world_possible s hw⟩,
   fun ⟨hs, hmax, hpos⟩ => maximal_possible_is_world s hs hmax hpos⟩

/--
  The actual world is a situation whose truths are exactly what
  obtains at the actual index.

  This is the one postulate of this file: it identifies the
  designated constant `actualWorld`, used both as a situation and as
  the index of evaluation, with a world faithful to that index.
-/
axiom actualWorld_faithful :
  Situation actualWorld ∧ ∀ p : Propn, (actualWorld ⊨ p) ↔ Obtains actualWorld p

/-- The actual world is a world. -/
theorem actualWorld_is_world : Worldhood actualWorld :=
  ⟨actualWorld_faithful.1,
   (Diamond_iff_exists _ _).mpr ⟨actualWorld, R_refl actualWorld, actualWorld_faithful.2⟩⟩

/-- The actual world is actual. -/
theorem actualWorld_actual : Actual actualWorld :=
  fun p => (actualWorld_faithful.2 p).mp

/--
  No proper part of a world is itself a world.

  If s is a world and x is a strict part of s (part but not equal),
  then x is not a world.  Worlds are the maximal situations.
-/
theorem no_strict_subworld :
    ∀ (w x : World),
      Worldhood w →
      (x ⊴ w) →
      x ≠ w →
      ¬ Worldhood x := by
  intro w x hw hxw hne hwx
  have hmx := world_maximal x hwx
  have hmw := world_maximal w hw
  apply hne
  apply situation_extensionality_via_truth x w hwx.1 hw.1
  intro p
  constructor
  · intro hp
    cases hmw p with
    | inl h => exact h
    | inr h =>
      -- h : w ⊨ ¬ₚp, but hxw : x ⊴ w and hp : x ⊨ p,
      -- so part_truth_mono gives w ⊨ p, contradicting world_TrueIn_neg.
      exact absurd
        (part_truth_mono x w hwx.1 hw.1 hxw p hp)
        ((world_TrueIn_neg w hw p).mp h)
  · intro hp
    -- hxw goes x ⊴ w, not w ⊴ x, so part_truth_mono cannot transfer hp
    -- directly. Use maximality of x: x ⊨ p ∨ x ⊨ ¬ₚp. If x ⊨ ¬ₚp then
    -- part_truth_mono gives w ⊨ ¬ₚp, so world_TrueIn_neg gives ¬(w ⊨ p),
    -- contradicting hp. Hence x ⊨ p.
    cases hmx p with
    | inl h => exact h
    | inr h =>
      exact absurd hp
        ((world_TrueIn_neg w hw p).mp
          (part_truth_mono x w hwx.1 hw.1 hxw (¬ₚ p) h))

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
  apply Classical.byContradiction
  intro hall
  apply hne
  apply situation_extensionality_via_truth w₁ w₂ hw₁.1 hw₂.1
  intro p
  apply iff_of_eq
  exact Classical.byContradiction fun hp => hall ⟨p, hp⟩

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
  apply situation_extensionality_via_truth w₁ w₂ hw₁.1 hw₂.1
  intro p
  constructor
  · exact part_truth_mono w₁ w₂ hw₁.1 hw₂.1 hpart p
  · intro hp
    cases world_maximal w₁ hw₁ p with
    | inl h  => exact h
    | inr hn =>
      exact absurd ⟨p, hp, part_truth_mono w₁ w₂ hw₁.1 hw₂.1 hpart (¬ₚ p) hn⟩
        (world_consistent w₂ hw₂)
