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

-- No axiom beyond the primitives is used.
#print axioms everythingActuallyConcrete_not_necessary
#print axioms sat_quantTheoryModel
