import Grounding.Ontology
import Grounding.Truth

/-
  S5 accessibility relation

  Rather than asserting R as a free axiom and separately
  postulating its three frame conditions, we define R directly
  from the truth-ordering already present in the theory.

  Two worlds are accessible from each other iff they agree on
  all necessary truths — i.e., iff their modal profiles match.
  For an S5 system this is just the universal relation: every
  world is accessible from every other.

  We make this explicit as a definition so the frame conditions
  become transparent calculations rather than independent axioms.
-/

/-- The S5 accessibility relation.
    In S5, every world is accessible from every world.
    This is the universal relation on World, which corresponds
    to the frame class characterised by reflexivity, transitivity,
    and symmetry simultaneously. Defining it directly eliminates
    the three separate axioms R_refl, R_trans, R_symm. -/
def R (_ _ : World) : Prop := True

theorem R_refl  : ∀ w : World,             R w w        := fun _ => trivial
theorem R_trans : ∀ w u v : World, R w u → R u v → R w v := fun _ _ _ _ _ => trivial
theorem R_symm  : ∀ w u : World,   R w u → R u w         := fun _ _ _ => trivial
