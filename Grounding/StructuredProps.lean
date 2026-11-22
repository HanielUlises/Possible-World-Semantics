import Grounding.Ontology
import Grounding.Truth
import Grounding.Parthood
import Situation.Theorems

namespace StructuredSemantics

/-- An infon is a structured proposition consisting of a relation,
    a sequence of argument positions, and a polarity.
    Infons are the elementary informational units of situation semantics
    in the sense of Barwise and Perry: they represent facts that situations
    can support, independently of any particular world making them true. -/
structure Infon where
  rel      : Property
  args     : List World
  polarity : Bool

/-- A situation supports an infon when the infon's relation is encoded
    by the situation and the polarity conditions on its arguments are met.
    Support is the primitive obtaining-relation of situation semantics,
    replacing the truth-at-world relation for sub-world informational units. -/
def Supports (s : World) (i : Infon) : Prop :=
  Situation s ∧ Enc s i.rel ∧
  (i.polarity = true → ∀ x ∈ i.args, Object x)

/-- A minimal supporting situation for an infon is one that supports it
    and is a part of every other supporting situation.
    Minimal situations individuate the exact informational content of an infon
    without extraneous facts, corresponding to the notion of a fact in
    the fine-grained ontology of situations. -/
def MinimalFor (i : Infon) (s : World) : Prop :=
  Supports s i ∧ ∀ s' : World, Situation s' → Supports s' i → (s ⊴ s')

/-- The join of two situations is their least upper bound in the
    parthood order.  It is defined by comprehension: the abstract
    object that encodes exactly the properties encoded by either
    component.  Its existence and lattice properties, formerly
    postulated, are theorems. -/
noncomputable def SitJoin (s s' : World) : World :=
  Classical.choose (Comprehension (fun F => Enc s F ∨ Enc s' F))

/-- The defining property of the join. -/
theorem SitJoin_spec (s s' : World) :
    A! (SitJoin s s') ∧ ∀ F : Property, Enc (SitJoin s s') F ↔ (Enc s F ∨ Enc s' F) :=
  Classical.choose_spec (Comprehension (fun F => Enc s F ∨ Enc s' F))

/-- The join of two situations is itself a situation.
    Informational content is closed under combination. -/
theorem SitJoin_situation : ∀ s s' : World,
    Situation s → Situation s' → Situation (SitJoin s s') :=
  fun s s' hs hs' => ⟨(SitJoin_spec s s').1, fun F hF =>
    (((SitJoin_spec s s').2 F).mp hF).elim (hs.2 F) (hs'.2 F)⟩

/-- The left component is a part of the join.
    The join extends each constituent situation. -/
theorem SitJoin_left : ∀ s s' : World, (s ⊴ SitJoin s s') :=
  fun s s' F hF => ((SitJoin_spec s s').2 F).mpr (Or.inl hF)

/-- The right component is a part of the join. -/
theorem SitJoin_right : ∀ s s' : World, (s' ⊴ SitJoin s s') :=
  fun s s' F hF => ((SitJoin_spec s s').2 F).mpr (Or.inr hF)

/-- The join is the least upper bound: any situation containing both
    components also contains their join.
    This is the universal property of the join as a binary supremum
    in the partial order of situations ordered by parthood. -/
theorem SitJoin_minimal : ∀ s s' u : World,
    (s ⊴ u) → (s' ⊴ u) → (SitJoin s s' ⊴ u) :=
  fun s s' _ h₁ h₂ F hF => (((SitJoin_spec s s').2 F).mp hF).elim (h₁ F) (h₂ F)

/-- The join inherits support from its left component.
    Any infon supported by a situation is also supported by any larger situation,
    reflecting the persistence or monotonicity of informational support
    under the parthood relation. -/
theorem SitJoin_supports_left (s s' : World) (i : Infon)
    (hs : Situation s) (hs' : Situation s')
    (h : Supports s i) : Supports (SitJoin s s') i := by
  obtain ⟨_, henc, hpol⟩ := h
  exact ⟨SitJoin_situation s s' hs hs',
         SitJoin_left s s' i.rel henc,
         hpol⟩

/-- Support is preserved under join from either component.
    If either constituent situation supports an infon, their combination does too.
    This reflects the monotone growth of informational content under merging. -/
theorem SitJoin_supports_either (s s' : World) (i : Infon)
    (hs : Situation s) (hs' : Situation s') :
    Supports s i ∨ Supports s' i → Supports (SitJoin s s') i := by
  rintro (h | h)
  · exact SitJoin_supports_left s s' i hs hs' h
  · obtain ⟨_, henc, hpol⟩ := h
    exact ⟨SitJoin_situation s s' hs hs',
           SitJoin_right s s' i.rel henc,
           hpol⟩

/-- The join operation is commutative up to situational identity.
    The combined informational content of s and s' is the same regardless
    of the order in which the components are named.
    Commutativity here is not trivial but requires situation extensionality
    to promote propositional equivalence to identity. -/
theorem SitJoin_comm (s s' : World)
    (hs : Situation s) (hs' : Situation s') :
    SitJoin s s' = SitJoin s' s := by
  apply situation_extensionality_via_truth
  · exact SitJoin_situation s s' hs hs'
  · exact SitJoin_situation s' s hs' hs
  · intro p
    constructor
    · intro h
      exact (parthood_iff_truth_inclusion (SitJoin s s') (SitJoin s' s)
              (SitJoin_situation s s' hs hs')
              (SitJoin_situation s' s hs' hs)).mp
            (SitJoin_minimal s s' (SitJoin s' s)
              (SitJoin_right s' s) (SitJoin_left s' s)) p h
    · intro h
      exact (parthood_iff_truth_inclusion (SitJoin s' s) (SitJoin s s')
              (SitJoin_situation s' s hs' hs)
              (SitJoin_situation s s' hs hs')).mp
            (SitJoin_minimal s' s (SitJoin s s')
              (SitJoin_right s s') (SitJoin_left s s')) p h

end StructuredSemantics
