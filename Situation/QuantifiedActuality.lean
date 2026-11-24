import Modality.QuantifiedActuality
import Situation.Actuality

/-
  QUANTIFIED ACTUALITY IN THE THEORY

  The quantifiers of the development, like those of Zalta's theory,
  are possibilist: they range over the single domain `World`, which is
  the same at every index.  Concreteness, however, is relative to an
  index (`Concrete v x`), so the objects that are concrete at an index
  form a domain that may vary from index to index.  Actualist
  quantification is quantification restricted to that domain:

    ∀ᶜx φ  at v   :=   ∀x (Concrete v x → φ)

  With it, the quantified contingent logical truths of
  Modality/QuantifiedActuality.lean arise within the theory, and no
  axiom is added:

  * `everythingActuallyConcrete_actual`: "everything concrete is
    actually concrete" holds at the actual index, by definition alone;
  * `box_everythingActuallyConcrete_iff`: its necessitation holds
    exactly when nothing could be concrete without being actually
    concrete, so `everythingActuallyConcrete_not_necessary`: if
    something could have been concrete that is not actually concrete,
    it is not necessary;
  * the same holds for the commutation of 𝒜 with the actualist
    quantifier (`concreteCommute_actual`,
    `concreteCommute_not_necessary`), whereas "everything concrete is
    concrete" is necessary (`box_everythingConcrete`);
  * the possibilist quantifier satisfies the Barcan formula and its
    converse (`possibilist_barcan`), whereas for the actualist
    quantifier the Barcan formula holds exactly when no possible
    domain exceeds the domain at the index (`barcan_iff`), and the
    converse exactly when the domain at the index is included in every
    possible domain (`converseBarcan_iff`);
  * `quantTheoryModel` reads the development as a model of the
    quantified deep embedding, with the concrete objects at an index
    as its domain, and `sat_quantTheoryModel` shows that the two
    treatments agree.

  The theory does not decide whether the domain varies.
  `Model/Satisfiable.lean` exhibits a model of all the axioms in which
  something could have been concrete that is not actually concrete, so
  there the necessitation fails (`Model.quantified_contingent_logical_truth`),
  and both Barcan formulas fail (`Model.barcan_fails`,
  `Model.converseBarcan_fails`).
-/

/-- Actualist universal quantification: φ holds, at the index v, of
    every object concrete at v. -/
def AllConcrete (φ : World → World → Prop) : World → Prop :=
  fun v => ∀ x : World, Concrete v x → φ x v

/-- Everything concrete is actually concrete: `∀ᶜx 𝒜E!x`. -/
def EverythingActuallyConcrete : World → Prop :=
  AllConcrete (fun x => 𝒜 (fun v => Concrete v x))

/-- Commutation of actuality with the actualist quantifier:
    `𝒜∀ᶜxφ ↔ ∀ᶜx𝒜φ`. -/
def ConcreteCommute (φ : World → World → Prop) : World → Prop :=
  fun w => 𝒜 (AllConcrete φ) w ↔ AllConcrete (fun x => 𝒜 (φ x)) w

/-! ## Everything is actually concrete -/

/-- At the actual index, everything concrete is actually concrete. -/
theorem everythingActuallyConcrete_actual :
    EverythingActuallyConcrete actualIndex :=
  fun _ h => h

/-- The necessitation holds exactly when nothing could be concrete
    without being actually concrete. -/
theorem box_everythingActuallyConcrete_iff (w : World) :
    □ EverythingActuallyConcrete w ↔
      ∀ v x : World, Concrete v x → Concrete actualIndex x :=
  ⟨fun h v x hx => h v trivial x hx, fun h v _ x hx => h v x hx⟩

/-- A quantified contingent logical truth: if something could have been
    concrete that is not actually concrete, then "everything concrete
    is actually concrete", which holds at the actual index, is not
    necessary. -/
theorem everythingActuallyConcrete_not_necessary (w : World)
    (h : ∃ v x : World, Concrete v x ∧ ¬ Concrete actualIndex x) :
    ¬ □ EverythingActuallyConcrete w := by
  rw [box_everythingActuallyConcrete_iff]
  obtain ⟨v, x, hx, hnx⟩ := h
  exact fun hall => hnx (hall v x hx)

/-- Everything concrete is concrete, necessarily: the actualist
    quantifier ranges over what is concrete. -/
theorem box_everythingConcrete (w : World) :
    □ (AllConcrete (fun x v => Concrete v x)) w :=
  fun _ _ _ hx => hx

/-! ## Actuality and the actualist quantifier -/

/-- At the actual index, 𝒜 commutes with the actualist quantifier. -/
theorem concreteCommute_actual (φ : World → World → Prop) :
    ConcreteCommute φ actualIndex :=
  Iff.rfl

/-- If the domain is the same at every index, the commutation holds at
    every index. -/
theorem concreteCommute_constant (φ : World → World → Prop) (w : World)
    (hc : ∀ x : World, Concrete w x ↔ Concrete actualIndex x) :
    ConcreteCommute φ w :=
  forall_congr' fun x => imp_congr (hc x).symm Iff.rfl

/-- At an index where something is concrete that is not actually
    concrete, 𝒜 does not commute with the actualist quantifier. -/
theorem concreteCommute_fails (v x : World) (hx : Concrete v x)
    (hnx : ¬ Concrete actualIndex x) :
    ¬ ConcreteCommute (fun y u => Concrete u y) v :=
  fun h => hnx ((h.mp (fun _ hy => hy)) x hx)

/-- If something could have been concrete that is not actually
    concrete, the commutation, which holds at the actual index, is not
    necessary. -/
theorem concreteCommute_not_necessary (w : World)
    (h : ∃ v x : World, Concrete v x ∧ ¬ Concrete actualIndex x) :
    ¬ □ (ConcreteCommute (fun y u => Concrete u y)) w := by
  obtain ⟨v, x, hx, hnx⟩ := h
  exact fun hbox => concreteCommute_fails v x hx hnx (hbox v trivial)

/-! ## The Barcan formulas

  The possibilist quantifier over `World` satisfies both the Barcan
  formula and its converse, as in the simplest quantified modal logic
  defended by Linsky and Zalta.  For the actualist quantifier each
  formula corresponds to a condition on the domains of concrete
  objects: the Barcan formula to every possible domain being included
  in the domain at the index, and the converse to the domain at the
  index being included in every possible domain.
-/

/-- The Barcan formula for the actualist quantifier:
    `∀ᶜx □φ → □∀ᶜx φ`. -/
def Barcan (φ : World → World → Prop) : World → Prop :=
  fun w => (∀ x : World, Concrete w x → □ (φ x) w) → □ (AllConcrete φ) w

/-- The converse Barcan formula for the actualist quantifier:
    `□∀ᶜx φ → ∀ᶜx □φ`. -/
def ConverseBarcan (φ : World → World → Prop) : World → Prop :=
  fun w => □ (AllConcrete φ) w → ∀ x : World, Concrete w x → □ (φ x) w

/-- The possibilist quantifier commutes with □: both the Barcan formula
    and its converse hold. -/
theorem possibilist_barcan (φ : World → World → Prop) (w : World) :
    (∀ x : World, □ (φ x) w) ↔ □ (fun v => ∀ x : World, φ x v) w :=
  ⟨fun h v hv x => h x v hv, fun h x v hv => h v hv x⟩

/-- The Barcan formula holds at w for every condition exactly when
    whatever could be concrete is concrete at w. -/
theorem barcan_iff (w : World) :
    (∀ φ : World → World → Prop, Barcan φ w) ↔
      ∀ v x : World, Concrete v x → Concrete w x := by
  constructor
  · intro h v x hx
    exact h (fun y _ => Concrete w y) (fun _ hy _ _ => hy) v trivial x hx
  · intro h φ hφ v _ x hx
    exact hφ x (h v x hx) v trivial

/-- The converse Barcan formula holds at w for every condition exactly
    when whatever is concrete at w is concrete at every index. -/
theorem converseBarcan_iff (w : World) :
    (∀ φ : World → World → Prop, ConverseBarcan φ w) ↔
      ∀ v x : World, Concrete w x → Concrete v x := by
  constructor
  · intro h v x hx
    exact h (fun y u => Concrete u y) (box_everythingConcrete w) x hx v trivial
  · intro h φ hφ x hx v _
    exact hφ v trivial x (h v x hx)

/-- If something could be concrete without being concrete at w, the
    Barcan formula fails at w for the condition of being concrete at w. -/
theorem barcan_fails (w v x : World) (hx : Concrete v x) (hnx : ¬ Concrete w x) :
    ¬ Barcan (fun y _ => Concrete w y) w :=
  fun h => hnx (h (fun _ hy _ _ => hy) v trivial x hx)

/-- If something concrete at w could fail to be concrete, the converse
    Barcan formula fails at w for concreteness. -/
theorem converseBarcan_fails (w v x : World) (hx : Concrete w x)
    (hnx : ¬ Concrete v x) :
    ¬ ConverseBarcan (fun y u => Concrete u y) w :=
  fun h => hnx (h (box_everythingConcrete w) x hx v trivial)

/-! ## The development as a model of quantified modal logic -/

open QuantifiedActuality in
/-- The development read as a model of the quantified deep embedding:
    indices are worlds, accessibility is R, the actual world is
    `actualIndex`, the domain at an index is what is concrete there,
    and predicates are interpreted by I. -/
noncomputable def quantTheoryModel {π : Type}
    (I : π → World → List World → Prop) : QuantifiedActuality.Model π where
  W      := World
  R      := R
  actual := actualIndex
  D      := World
  dom    := fun v x => Concrete v x
  interp := I

open QuantifiedActuality in
/-- Translation of quantified formulas into conditions on worlds, with
    the quantifier read as `AllConcrete`. -/
def qinterp {π : Type} (I : π → World → List World → Prop) :
    QuantifiedActuality.Formula π → World → (Nat → World) → Prop
  | .pred P xs, v, g => I P v (xs.map g)
  | .eq x y,    _, g => g x = g y
  | .bot,       _, _ => False
  | .neg φ,     v, g => ¬ qinterp I φ v g
  | .conj φ ψ,  v, g => qinterp I φ v g ∧ qinterp I ψ v g
  | .impl φ ψ,  v, g => qinterp I φ v g → qinterp I ψ v g
  | .all x φ,   v, g => AllConcrete (fun d u => qinterp I φ u (update g x d)) v
  | .box φ,     v, g => □ (fun u => qinterp I φ u g) v
  | .act φ,     v, g => 𝒜 (fun u => qinterp I φ u g) v

open QuantifiedActuality in
/-- The deep and shallow treatments agree: truth in `quantTheoryModel`
    is the shallow interpretation, with ∀ as `AllConcrete`, 𝒜 as
    `Actually` and □ as `Box`. -/
theorem sat_quantTheoryModel {π : Type} (I : π → World → List World → Prop)
    (φ : QuantifiedActuality.Formula π) (v : World) (g : Nat → World) :
    sat (quantTheoryModel I) φ v g ↔ qinterp I φ v g := by
  induction φ generalizing v g with
  | pred P xs => exact Iff.rfl
  | eq x y => exact Iff.rfl
  | bot => exact Iff.rfl
  | neg φ ih => exact not_congr (ih v g)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ v g) (ihψ v g)
  | impl φ ψ ihφ ihψ => exact imp_congr (ihφ v g) (ihψ v g)
  | all x φ ih => exact forall_congr' fun d => imp_congr Iff.rfl (ih v _)
  | box φ ih => exact forall_congr' fun u => imp_congr Iff.rfl (ih u g)
  | act φ ih => exact ih actualIndex g

open QuantifiedActuality in
/-- The development's quantified model is universal. -/
theorem quantTheoryModel_universal {π : Type} (I : π → World → List World → Prop) :
    UniversalModels (quantTheoryModel I) :=
  fun _ _ => trivial

open QuantifiedActuality in
/-- Every real-world valid quantified formula over universal models
    holds at the actual index of the development, under every
    interpretation of the predicates and every assignment. -/
theorem rwValid_holds_actually_quantified {π : Type}
    (φ : QuantifiedActuality.Formula π) (h : RWValid UniversalModels φ)
    (I : π → World → List World → Prop) (g : Nat → World) :
    qinterp I φ actualIndex g :=
  (sat_quantTheoryModel I φ actualIndex g).mp
    (h (quantTheoryModel I) (quantTheoryModel_universal I) g)

open QuantifiedActuality in
/-- The deep formula "everything actually exists", in the development,
    says that everything concrete is actually concrete. -/
theorem sat_allActual_theory {π : Type} (I : π → World → List World → Prop)
    (w : World) (g : Nat → World) :
    sat (quantTheoryModel I) Formula.allActual w g ↔ EverythingActuallyConcrete w :=
  sat_allActual (quantTheoryModel I) w g
