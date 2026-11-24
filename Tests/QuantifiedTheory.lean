-- Tests/QuantifiedTheory.lean
import Situation.QuantifiedActuality

-- In the development, everything concrete is actually concrete at the
-- actual index, and not necessarily so if something could have been
-- concrete without actually being so.
example : EverythingActuallyConcrete actualIndex :=
  everythingActuallyConcrete_actual

example (h : ∃ v x : World, Concrete v x ∧ ¬ Concrete actualIndex x) :
    ¬ □ EverythingActuallyConcrete actualIndex :=
  everythingActuallyConcrete_not_necessary actualIndex h

-- Everything concrete is necessarily concrete.
example : □ (AllConcrete (fun x v => Concrete v x)) actualIndex :=
  box_everythingConcrete actualIndex

-- Real-world valid quantified formulas hold at the actual index; in
-- particular "everything actually exists" does.
example (I : Nat → World → List World → Prop) (g : Nat → World) :
    qinterp I QuantifiedActuality.Formula.allActual actualIndex g :=
  rwValid_holds_actually_quantified _
    (QuantifiedActuality.allActual_rwValid _) I g

-- The possibilist quantifier satisfies the Barcan formulas; for the
-- actualist quantifier they correspond to conditions on the domains.
example (φ : World → World → Prop) (w : World) :
    (∀ x : World, □ (φ x) w) ↔ □ (fun v => ∀ x : World, φ x v) w :=
  possibilist_barcan φ w

example (w : World) :
    (∀ φ : World → World → Prop, Barcan φ w) ↔
      ∀ v x : World, Concrete v x → Concrete w x :=
  barcan_iff w

example (w : World) :
    (∀ φ : World → World → Prop, ConverseBarcan φ w) ↔
      ∀ v x : World, Concrete w x → Concrete v x :=
  converseBarcan_iff w

-- No axiom beyond the primitives is used.
#print axioms barcan_iff
#print axioms converseBarcan_iff
#print axioms everythingActuallyConcrete_not_necessary
#print axioms sat_quantTheoryModel
