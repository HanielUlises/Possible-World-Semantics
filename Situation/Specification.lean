import Spec.Theory
import Grounding
import Modality
import Situation.Definitions
import Situation.Extensionality
import Situation.Derived
import Situation.Theorems
import Situation.Infimum
import Situation.Worlds
import Situation.Actuality
import Situation.Variants
import Situation.QuantifiedActuality

/-
  THE DEVELOPMENT AS AN INSTANCE OF `Spec.Theory`

  `developmentTheory` fills every field of `Spec.Theory` with the axiom
  of the same name.  Lean therefore checks that each axiom has exactly
  the statement of its field.  `rfl` lemmas show that the definitions
  of the development coincide with those of `Spec.Theory`.

  The command `#check_axioms_are_fields` (Spec/Check.lean), run in
  Tests/Specification.lean after every library has been imported,
  checks the converse: every
  `axiom` declared in Grounding/, Modality/ and Situation/ is a field,
  every field is filled by the axiom of its name, and every source file
  of those libraries is imported, so that no axiom is missed.
-/

/-- The development, as a theory: every field is the axiom of the same
    name. -/
noncomputable def developmentTheory : Spec.Theory where
  World := _root_.World
  Property := _root_.Property
  Propn := _root_.Propn
  Enc := _root_.Enc
  Encp := _root_.Encp
  VAC := _root_.VAC
  Concrete := _root_.Concrete
  neg := _root_.neg
  conj := _root_.conj
  disj := _root_.disj
  impl := _root_.impl
  bic := _root_.bic
  bic_def := _root_.bic_def
  neg_neg := _root_.neg_neg
  deMorgan_conj := _root_.deMorgan_conj
  deMorgan_disj := _root_.deMorgan_disj
  impl_as_disj := _root_.impl_as_disj
  conj_comm := _root_.conj_comm
  disj_comm := _root_.disj_comm
  conj_assoc := _root_.conj_assoc
  disj_assoc := _root_.disj_assoc
  TrueIn := _root_.TrueIn
  Encp_def := _root_.Encp_def
  TrueIn_def := _root_.TrueIn_def
  Obtains := _root_.Obtains
  Obtains_neg := _root_.Obtains_neg
  Obtains_conj := _root_.Obtains_conj
  Obtains_disj := _root_.Obtains_disj
  Obtains_impl := _root_.Obtains_impl
  VAC_congr := _root_.VAC_congr
  ordinary_no_encoding := _root_.ordinary_no_encoding
  Comprehension := _root_.Comprehension
  abstract_extensionality := _root_.abstract_extensionality
  actualIndex := _root_.actualIndex

/-! ## The definitions of the development are those of `Spec.Theory` -/

namespace Specification

theorem R_eq : (R : World → World → Prop) = Spec.R := rfl
theorem Box_eq : (Box : (World → Prop) → World → Prop) = Spec.Box := rfl
theorem Diamond_eq : (Diamond : (World → Prop) → World → Prop) = Spec.Diamond := rfl
theorem OrdinaryObject_eq : OrdinaryObject = Spec.OrdinaryObject Concrete := rfl
theorem AbstractObject_eq : AbstractObject = Spec.AbstractObject Concrete := rfl
theorem Object_eq : Object = Spec.Object Concrete := rfl
theorem Situation_eq : Situation = developmentTheory.Situation := rfl
theorem PartOf_eq : PartOf = developmentTheory.PartOf := rfl
theorem Agree_eq : Agree = developmentTheory.Agree := rfl
theorem ExtEq_eq : ExtEq = developmentTheory.ExtEq := rfl
theorem actualWorld_eq : actualWorld = developmentTheory.actualWorld := rfl
theorem Actual_eq : Actual = developmentTheory.Actual := rfl
theorem Possible_eq : Possible = developmentTheory.Possible := rfl
theorem Worldhood_eq : Worldhood = developmentTheory.Worldhood := rfl
theorem Maximal₁_eq : Maximal₁ = developmentTheory.Maximal₁ := rfl
theorem Partial₁_eq : Partial₁ = developmentTheory.Partial₁ := rfl
theorem Consistent_eq : Consistent = developmentTheory.Consistent := rfl
theorem Actually_eq : Actually = developmentTheory.Actually := rfl
theorem AllConcrete_eq : AllConcrete = developmentTheory.AllConcrete := rfl
theorem EverythingActuallyConcrete_eq :
    EverythingActuallyConcrete = developmentTheory.EverythingActuallyConcrete := rfl
theorem Barcan_eq : Barcan = developmentTheory.Barcan := rfl
theorem ConverseBarcan_eq : ConverseBarcan = developmentTheory.ConverseBarcan := rfl

end Specification
