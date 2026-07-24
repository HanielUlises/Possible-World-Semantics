import Grounding.Ontology
import Grounding.Truth

/-
  DERIVED RELATIONS ON SITUATIONS

  These notions are defined in terms of truth-in.
  They introduce no new ontology and no modal structure.
-/

/--
  Truth agreement between two situations.

  s and s' agree iff they make exactly the same
  propositions true.
-/
def Agree (s s' : World) : Prop :=
  ∀ p : Propn, (s ⊨ p) ↔ (s' ⊨ p)

/--
  Extensional equivalence of situations.

  This is truth-based equivalence restricted
  to objects that are situations.
-/
def ExtEq (s s' : World) : Prop :=
  Situation s ∧ Situation s' ∧ Agree s s'

/--
  Truth agreement is reflexive.
-/
theorem agree_refl (s : World) : Agree s s :=
  fun _ => Iff.rfl

/--
  Truth agreement is symmetric.
-/
theorem agree_symm (s s' : World) (h : Agree s s') : Agree s' s :=
  fun p => (h p).symm

/--
  Truth agreement is transitive.
-/
theorem agree_trans (s s' s'' : World)
    (h : Agree s s') (h' : Agree s' s'') : Agree s s'' :=
  fun p => (h p).trans (h' p)
