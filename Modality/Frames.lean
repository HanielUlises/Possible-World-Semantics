import Grounding.Ontology

/-
  KRIPKE FRAMES

  A Kripke frame consists of a set of worlds together
  with an accessibility relation.

  In S5, every world accesses every world, the accessibility
  relation is the universal relation on World. Rather than
  postulating R as a free axiom and separately asserting its
  three frame conditions, we define R directly as the
  constant-true relation. The three conditions then hold by
  computation rather than by fiat, reducing the axiom count
  in this file from four to zero.

  No modal principles are assumed at this level.
-/

/--
  Accessibility relation between worlds.

  Defined as the universal relation: in S5, every world is
  accessible from every world. The three frame conditions
  (reflexivity, transitivity, symmetry) are immediate from
  this definition and need not be separately postulated.
-/
def R (_ _ : World) : Prop := True

/--
  Reflexivity of accessibility.

  Every world accesses itself.
  Holds by definition of R.
-/
theorem R_refl : ∀ w : World, R w w :=
  fun _ => trivial

/--
  Transitivity of accessibility.

  Accessibility is closed under chaining.
  Holds by definition of R.
-/
theorem R_trans : ∀ w u v : World, R w u → R u v → R w v :=
  fun _ _ _ _ _ => trivial

/--
  Symmetry of accessibility.

  Accessibility is bidirectional.
  Holds by definition of R.
-/
theorem R_symm : ∀ w u : World, R w u → R u w :=
  fun _ _ _ => trivial
