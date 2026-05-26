import Grounding.Ontology
import Grounding.Truth
import Situation.Derived
import Situation.Extensionality

def PartOf (x y : World) : Prop :=
  ∀ F : Property, Enc x F → Enc y F

notation:15 x " ⊴ " y => PartOf x y

theorem partOf_refl (x : World) : x ⊴ x :=
  fun _ h => h

theorem partOf_trans (x y z : World) (hxy : x ⊴ y) (hyz : y ⊴ z) : x ⊴ z :=
  fun F hxF => hyz F (hxy F hxF)

theorem partOf_antisymm_enc (x y : World) (hxy : x ⊴ y) (hyx : y ⊴ x) (F : Property) :
    Enc x F ↔ Enc y F :=
  ⟨fun h => hxy F h, fun h => hyx F h⟩

/-
  Open proof obligation OP-2: Parthood via truth-monotonicity.
  See README.md § Open Proof Obligations, OP-2.
-/

/-- Auxiliary: parthood implies truth-monotonicity.
    If s ⊴ s' then every proposition true in s is true in s'.
    Resolves OP-3 via situation_is_object. -/
theorem part_truth_mono (s s' : World)
    (hs   : Situation s)
    (hs'  : Situation s')
    (hss' : s ⊴ s')
    (p    : Propn)
    (hp   : s ⊨ p) : s' ⊨ p := by
  have hobs  : Object s  := situation_is_object s hs
  have hobs' : Object s' := situation_is_object s' hs'
  rw [TrueIn_def s' p hobs']
  rw [TrueIn_def s p hobs] at hp
  rw [Encp_def s p hobs] at hp
  rw [Encp_def s' p hobs']
  obtain ⟨F, hF, henc⟩ := hp
  exact ⟨F, hF, hss' F henc⟩

/-- Theorem 4 (Zalta 1993): parthood is equivalent to truth inclusion.
    The (<=) direction requires truth_mono_to_part (OP-2).
    Blocked by OP-2. See README.md § Open Proof Obligations. -/
theorem parthood_iff_truth_inclusion (s s' : World)
    (hs  : Situation s)
    (hs' : Situation s') :
    (s ⊴ s') ↔ (∀ p : Propn, (s ⊨ p) → (s' ⊨ p)) := by
  constructor
  · intro h p hp
    exact part_truth_mono s s' hs hs' h p hp
  · intro h
    sorry -- OP-2: requires truth_mono_to_part

/-- Theorem 5 (Zalta 1993): mutual parthood entails identity.
    Blocked by OP-2. -/
theorem parthood_antisymm (s s' : World)
    (hs   : Situation s)
    (hs'  : Situation s')
    (hss' : s ⊴ s')
    (hs's : s' ⊴ s) : s = s' := by
  apply situation_extensionality
  exact ⟨hs, hs', fun p =>
    ⟨part_truth_mono s s' hs hs' hss' p,
     part_truth_mono s' s hs' hs hs's p⟩⟩

/-- Theorem 6 (Zalta 1993): same parts entails identity.
    Follows from Theorem 5 once OP-2 is resolved. -/
theorem same_parts_identity (s s' : World)
    (hs  : Situation s)
    (hs' : Situation s')
    (h   : ∀ s'' : World, (s'' ⊴ s) ↔ (s'' ⊴ s')) : s = s' := by
  apply parthood_antisymm s s' hs hs'
  · exact (h s).mp (partOf_refl s)
  · exact (h s').mpr (partOf_refl s')

    /-- If every proposition true in s is true in s', then s is a part of s'.
    This closes OP-2. The proof unfolds TrueIn through Encp_def and
    Enc_VAC_complete to show that every property encoded by s is of
    the form VAC p, and therefore also encoded by s'. -/
theorem truth_mono_to_part (s s' : World)
    (hs  : Situation s)
    (hs' : Situation s')
    (h   : ∀ p : Propn, (s ⊨ p) → (s' ⊨ p)) : (s ⊴ s') := by
  intro F hF
  obtain ⟨p, rfl⟩ := Enc_VAC_complete s F hs hF
  have hobs  := situation_is_object s hs
  have hobs' := situation_is_object s' hs'
  have hsp : s ⊨ p := by
    rw [TrueIn_def s p hobs]
    rw [Encp_def s p hobs]
    exact ⟨VAC p, rfl, hF⟩
  have hs'p := h p hsp
  rw [TrueIn_def s' p hobs'] at hs'p
  rw [Encp_def s' p hobs'] at hs'p
  obtain ⟨F', hF', henc⟩ := hs'p
  rwa [← hF'] at henc

theorem parthood_iff_truth_inclusion (s s' : World)
    (hs  : Situation s)
    (hs' : Situation s') :
    (s ⊴ s') ↔ (∀ p : Propn, (s ⊨ p) → (s' ⊨ p)) :=
  ⟨fun h p hp => part_truth_mono s s' hs hs' h p hp,
   fun h      => truth_mono_to_part s s' hs hs' h⟩

theorem parthood_antisymm (s s' : World)
    (hs   : Situation s)
    (hs'  : Situation s')
    (hss' : s ⊴ s')
    (hs's : s' ⊴ s) : s = s' := by
  apply situation_extensionality
  exact ⟨hs, hs', fun p =>
    ⟨part_truth_mono s s' hs hs' hss' p,
     part_truth_mono s' s hs' hs hs's p⟩⟩

theorem same_parts_identity (s s' : World)
    (hs  : Situation s)
    (hs' : Situation s')
    (h   : ∀ s'' : World, (s'' ⊴ s) ↔ (s'' ⊴ s')) : s = s' :=
  parthood_antisymm s s' hs hs'
    ((h s).mp  (partOf_refl s))
    ((h s').mpr (partOf_refl s'))

    theorem all_propositions_persistent :
    ∀ p : Propn, Persistent p := by
  intro p s s' hsp hss'
  have hss : Situation s := situation_closed_under_parthood s' s
    (by sorry) hss' -- needs Situation s'
  exact part_truth_mono s s' hss
    (situation_closed_under_parthood s' s (by sorry) hss')
    hss' p hsp
