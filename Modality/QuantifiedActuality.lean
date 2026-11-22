/-
  QUANTIFIED MODAL LOGIC WITH ACTUALITY

  A deep embedding of first-order modal logic with an actuality
  operator 𝒜, interpreted in Kripke models with a designated actual
  world and variable domains.  The quantifier ∀x ranges over the
  objects that exist at the world of evaluation (actualist
  quantification); free variables may denote objects that do not exist
  there.  Existence is definable: `E x` is `¬∀y ¬(y = x)`.

  Real-world and general validity are defined as in
  Modality/ActualityLogic.lean, quantifying in addition over
  assignments.  The main results, each relative to an arbitrary class
  of models:

  * the closure properties of the propositional case carry over, and
    both notions are closed under universal generalization;
  * `φ ↔ 𝒜φ` is real-world valid, and `□(φ ↔ 𝒜φ)` holds at a world
    under an assignment exactly when φ, under that assignment, takes
    its actual value at every accessible world;
  * `𝒜∀xφ ↔ ∀x𝒜φ` is real-world valid, generally valid over
    constant-domain models, and neither generally valid nor
    necessarily true in any class containing a model whose domain
    grows beyond the actual one;
  * "everything actually exists", `∀x 𝒜E x`, is real-world valid; its
    necessitation holds at a world exactly when no accessible world
    has an object that does not actually exist; and it fails to be
    generally valid in the same classes, whereas `∀x E x` is generally
    valid in every model;
  * 𝒜 is inert for real-world validity, and general validity of 𝒜φ
    coincides with real-world validity of φ.

  The quantified contingent logical truths thus depend on the domains
  of the model, not only on which atomic facts are contingent.

  Nothing here depends on the axioms of the development; the file
  uses only Lean's own logic.
-/

namespace QuantifiedActuality

/-- Formulas over a type π of predicate symbols.  Variables are
    natural numbers. -/
inductive Formula (π : Type) where
  | pred : π → List Nat → Formula π
  | eq   : Nat → Nat → Formula π
  | bot  : Formula π
  | neg  : Formula π → Formula π
  | conj : Formula π → Formula π → Formula π
  | impl : Formula π → Formula π → Formula π
  | all  : Nat → Formula π → Formula π
  | box  : Formula π → Formula π
  | act  : Formula π → Formula π

namespace Formula

variable {π : Type}

/-- Material biconditional. -/
def iff (φ ψ : Formula π) : Formula π := conj (impl φ ψ) (impl ψ φ)

/-- Existence: something is identical to x. -/
def E (x : Nat) : Formula π := neg (all (x + 1) (neg (eq (x + 1) x)))

/-- Quantifier–actuality commutation: `𝒜∀xφ ↔ ∀x𝒜φ`. -/
def commute (x : Nat) (φ : Formula π) : Formula π :=
  iff (act (all x φ)) (all x (act φ))

/-- Everything actually exists: `∀x 𝒜E x`. -/
def allActual : Formula π := all 0 (act (E 0))

/-- Everything exists: `∀x E x`. -/
def allExist : Formula π := all 0 (E 0)

end Formula

open Formula

/-- A Kripke model with a designated actual world and variable
    domains.  `dom w d` holds when d exists at w. -/
structure Model (π : Type) where
  W      : Type
  R      : W → W → Prop
  actual : W
  D      : Type
  dom    : W → D → Prop
  interp : π → W → List D → Prop

variable {π : Type}

/-- The assignment that agrees with g except that it sends x to d. -/
def update {D : Type} (g : Nat → D) (x : Nat) (d : D) : Nat → D :=
  fun y => if y = x then d else g y

theorem update_same {D : Type} (g : Nat → D) (x : Nat) (d : D) :
    update g x d x = d :=
  if_pos rfl

theorem update_other {D : Type} (g : Nat → D) {x y : Nat} (d : D) (h : y ≠ x) :
    update g x d y = g y :=
  if_neg h

/-- Truth of a formula at a world of a model under an assignment. -/
def sat (M : Model π) : Formula π → M.W → (Nat → M.D) → Prop
  | pred P xs, w, g => M.interp P w (xs.map g)
  | eq x y,    _, g => g x = g y
  | bot,       _, _ => False
  | neg φ,     w, g => ¬ sat M φ w g
  | conj φ ψ,  w, g => sat M φ w g ∧ sat M ψ w g
  | impl φ ψ,  w, g => sat M φ w g → sat M ψ w g
  | all x φ,   w, g => ∀ d, M.dom w d → sat M φ w (update g x d)
  | box φ,     w, g => ∀ v, M.R w v → sat M φ v g
  | act φ,     _, g => sat M φ M.actual g

/-- A class of models. -/
abbrev ModelClass (π : Type) := Model π → Prop

/-- Every model. -/
def AllModels : ModelClass π := fun _ => True

/-- Models whose accessibility relation is universal. -/
def UniversalModels : ModelClass π := fun M => ∀ w v, M.R w v

/-- Models in which every world has the same domain. -/
def ConstantDomain : ModelClass π := fun M => ∀ w v d, M.dom w d ↔ M.dom v d

/-- Real-world validity: truth at the actual world of every model in C,
    under every assignment. -/
def RWValid (C : ModelClass π) (φ : Formula π) : Prop :=
  ∀ M, C M → ∀ g, sat M φ M.actual g

/-- General validity: truth at every world of every model in C, under
    every assignment. -/
def GValid (C : ModelClass π) (φ : Formula π) : Prop :=
  ∀ M, C M → ∀ w g, sat M φ w g

/-! ## Truth conditions of the derived formulas -/

theorem sat_iff (M : Model π) (φ ψ : Formula π) (w : M.W) (g : Nat → M.D) :
    sat M (iff φ ψ) w g ↔ (sat M φ w g ↔ sat M ψ w g) :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun h => ⟨h.mp, h.mpr⟩⟩

/-- `E x` holds at w exactly when the value of x exists at w. -/
theorem sat_E (M : Model π) (x : Nat) (w : M.W) (g : Nat → M.D) :
    sat M (E x) w g ↔ M.dom w (g x) := by
  have hx : x ≠ x + 1 := Nat.ne_of_lt (Nat.lt_succ_self x)
  show (¬ ∀ d, M.dom w d → ¬ (update g (x + 1) d (x + 1) = update g (x + 1) d x)) ↔ _
  simp only [update_same, update_other g _ hx]
  constructor
  · intro h
    exact Classical.byContradiction fun hn => h fun d hd he => hn (he ▸ hd)
  · exact fun h hall => hall (g x) h rfl

/-- `𝒜∀xφ ↔ ∀x𝒜φ` compares the actual domain with the domain of the
    world of evaluation. -/
theorem sat_commute (M : Model π) (x : Nat) (φ : Formula π) (w : M.W)
    (g : Nat → M.D) :
    sat M (commute x φ) w g ↔
      ((∀ d, M.dom M.actual d → sat M φ M.actual (update g x d)) ↔
        (∀ d, M.dom w d → sat M φ M.actual (update g x d))) :=
  sat_iff M _ _ w g

/-- `∀x 𝒜E x` holds at w exactly when everything that exists at w
    exists at the actual world. -/
theorem sat_allActual (M : Model π) (w : M.W) (g : Nat → M.D) :
    sat M allActual w g ↔ ∀ d, M.dom w d → M.dom M.actual d := by
  show (∀ d, M.dom w d → sat M (E 0) M.actual (update g 0 d)) ↔ _
  simp only [sat_E, update_same]

/-! ## Closure properties -/

/-- General validity implies real-world validity. -/
theorem GValid.rwValid {C : ModelClass π} {φ : Formula π}
    (h : GValid C φ) : RWValid C φ :=
  fun M hM g => h M hM M.actual g

/-- Real-world validity is closed under modus ponens. -/
theorem RWValid.mp {C : ModelClass π} {φ ψ : Formula π}
    (hφψ : RWValid C (impl φ ψ)) (hφ : RWValid C φ) : RWValid C ψ :=
  fun M hM g => hφψ M hM g (hφ M hM g)

/-- General validity is closed under modus ponens. -/
theorem GValid.mp {C : ModelClass π} {φ ψ : Formula π}
    (hφψ : GValid C (impl φ ψ)) (hφ : GValid C φ) : GValid C ψ :=
  fun M hM w g => hφψ M hM w g (hφ M hM w g)

/-- General validity is closed under necessitation. -/
theorem GValid.nec {C : ModelClass π} {φ : Formula π}
    (h : GValid C φ) : GValid C (box φ) :=
  fun M hM _ g v _ => h M hM v g

/-- Real-world validity is closed under universal generalization. -/
theorem RWValid.gen {C : ModelClass π} {φ : Formula π}
    (h : RWValid C φ) (x : Nat) : RWValid C (all x φ) :=
  fun M hM g d _ => h M hM (update g x d)

/-- General validity is closed under universal generalization. -/
theorem GValid.gen {C : ModelClass π} {φ : Formula π}
    (h : GValid C φ) (x : Nat) : GValid C (all x φ) :=
  fun M hM w g d _ => h M hM w (update g x d)

/-! ## The actuality truth -/

/-- `φ ↔ 𝒜φ` is real-world valid, for every formula and every class. -/
theorem actuality_rwValid (C : ModelClass π) (φ : Formula π) :
    RWValid C (iff φ (act φ)) :=
  fun M _ g => (sat_iff M φ (act φ) M.actual g).mpr Iff.rfl

/-- At a world w and under an assignment g, the necessitation of the
    actuality truth holds exactly when φ, under g, takes its actual
    value at every world accessible from w. -/
theorem sat_box_actuality (M : Model π) (φ : Formula π) (w : M.W)
    (g : Nat → M.D) :
    sat M (box (iff φ (act φ))) w g ↔
      ∀ v, M.R w v → (sat M φ v g ↔ sat M φ M.actual g) :=
  ⟨fun h v hv => (sat_iff M φ (act φ) v g).mp (h v hv),
   fun h v hv => (sat_iff M φ (act φ) v g).mpr (h v hv)⟩

/-! ## Quantifiers and actuality -/

/-- `𝒜∀xφ ↔ ∀x𝒜φ` is real-world valid, for every class. -/
theorem commute_rwValid (C : ModelClass π) (x : Nat) (φ : Formula π) :
    RWValid C (commute x φ) :=
  fun M _ g => (sat_commute M x φ M.actual g).mpr Iff.rfl

/-- Over constant-domain models, `𝒜∀xφ ↔ ∀x𝒜φ` is generally valid. -/
theorem commute_gValid_constant (x : Nat) (φ : Formula π) :
    GValid ConstantDomain (commute x φ) := by
  intro M hM w g
  rw [sat_commute]
  exact forall_congr' fun d => imp_congr (hM M.actual w d) Iff.rfl

/-- `∀x E x` is generally valid in every model: the quantifier ranges
    over what exists. -/
theorem allExist_gValid : GValid (AllModels (π := π)) allExist := by
  intro M _ w g d hd
  rw [sat_E, update_same]
  exact hd

/-- `∀x 𝒜E x` is real-world valid, for every class. -/
theorem allActual_rwValid (C : ModelClass π) : RWValid C allActual :=
  fun M _ g => (sat_allActual M M.actual g).mpr fun _ h => h

/-- The necessitation of `∀x 𝒜E x` holds at w exactly when every world
    accessible from w has only objects that actually exist. -/
theorem sat_box_allActual (M : Model π) (w : M.W) (g : Nat → M.D) :
    sat M (box allActual) w g ↔
      ∀ v, M.R w v → ∀ d, M.dom v d → M.dom M.actual d :=
  forall_congr' fun v => imp_congr Iff.rfl (sat_allActual M v g)

/-- Over constant-domain models, `∀x 𝒜E x` is generally valid. -/
theorem allActual_gValid_constant : GValid (ConstantDomain (π := π)) allActual :=
  fun M hM w g => (sat_allActual M w g).mpr fun d h => (hM w M.actual d).mp h

/-! ## A two-world countermodel with a growing domain -/

/-- Two mutually accessible worlds, `true` (actual) and `false`, over
    the objects `true` and `false`.  Only `true` exists at the actual
    world; both exist at the other. -/
def growing (π : Type) : Model π where
  W      := Bool
  R      := fun _ _ => True
  actual := true
  D      := Bool
  dom    := fun w d => w = true → d = true
  interp := fun _ _ _ => True

theorem growing_universal : UniversalModels (growing π) :=
  fun _ _ => trivial

/-- At the non-actual world of the countermodel, something exists that
    does not actually exist. -/
theorem growing_allActual_fails (g : Nat → Bool) :
    ¬ sat (growing π) allActual false g := by
  rw [sat_allActual]
  intro h
  exact Bool.noConfusion (h false (fun h' => Bool.noConfusion h') rfl)

/-- At the non-actual world of the countermodel, `𝒜∀x E x ↔ ∀x 𝒜E x`
    fails. -/
theorem growing_commute_fails (g : Nat → Bool) :
    ¬ sat (growing π) (commute 0 (E 0)) false g := by
  rw [sat_commute]
  intro h
  have hact : ∀ d, (growing π).dom (growing π).actual d →
      sat (growing π) (E 0) (growing π).actual (update g 0 d) := by
    intro d hd
    rw [sat_E, update_same]
    exact hd
  have hall := h.mp hact false (fun h' => Bool.noConfusion h')
  rw [sat_E, update_same] at hall
  exact Bool.noConfusion (hall rfl)

/-- For any class containing the countermodel, "everything actually
    exists" is not generally valid. -/
theorem allActual_not_gValid {C : ModelClass π} (hC : C (growing π)) :
    ¬ GValid C allActual :=
  fun h => growing_allActual_fails (fun _ => true) (h _ hC false _)

/-- For any class containing the countermodel, the necessitation of
    "everything actually exists" is not even real-world valid. -/
theorem box_allActual_not_rwValid {C : ModelClass π} (hC : C (growing π)) :
    ¬ RWValid C (box allActual) :=
  fun h => growing_allActual_fails (fun _ => true) (h _ hC _ false trivial)

/-- For any class containing the countermodel, the commutation of the
    quantifier with 𝒜 is not generally valid. -/
theorem commute_not_gValid {C : ModelClass π} (hC : C (growing π)) :
    ¬ GValid C (commute 0 (E 0)) :=
  fun h => growing_commute_fails (fun _ => true) (h _ hC false _)

/-- For any class containing the countermodel, the necessitation of the
    commutation is not even real-world valid. -/
theorem box_commute_not_rwValid {C : ModelClass π} (hC : C (growing π)) :
    ¬ RWValid C (box (commute 0 (E 0))) :=
  fun h => growing_commute_fails (fun _ => true) (h _ hC _ false trivial)

/-- A quantified contingent logical truth, over universal models: with
    variable domains, "everything actually exists" is real-world valid
    but its necessitation is not. -/
theorem quantified_contingent_logical_truth :
    RWValid (UniversalModels (π := π)) allActual ∧
    ¬ RWValid (UniversalModels (π := π)) (box allActual) :=
  ⟨allActual_rwValid _, box_allActual_not_rwValid growing_universal⟩

/-! ## Actuality is inert for real-world validity -/

/-- 𝒜φ is real-world valid exactly when φ is. -/
theorem rwValid_act_iff (C : ModelClass π) (φ : Formula π) :
    RWValid C (act φ) ↔ RWValid C φ :=
  Iff.rfl

/-- 𝒜φ is generally valid exactly when φ is real-world valid. -/
theorem gValid_act_iff (C : ModelClass π) (φ : Formula π) :
    GValid C (act φ) ↔ RWValid C φ :=
  ⟨fun h M hM g => h M hM M.actual g, fun h M hM _ g => h M hM g⟩

end QuantifiedActuality
