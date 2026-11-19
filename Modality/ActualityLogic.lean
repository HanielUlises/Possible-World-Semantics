/-
  THE LOGIC OF ACTUALITY: REAL-WORLD AND GENERAL VALIDITY

  A deep embedding of propositional modal logic with an actuality
  operator 𝒜, interpreted in Kripke models with a designated actual
  world (Crossley and Humberstone 1977).  Two notions of validity are
  compared (Davies and Humberstone 1980):

  * real-world validity: truth at the actual world of every model;
  * general validity: truth at every world of every model.

  The main results, each relative to an arbitrary class of models:

  * general validity implies real-world validity, and both are closed
    under modus ponens;
  * general validity is closed under necessitation, real-world
    validity is not;
  * `φ ↔ 𝒜φ` is real-world valid for every φ, but neither it nor its
    necessitation `□(φ ↔ 𝒜φ)` is generally valid, in any class of
    models containing a two-world model, which includes the S5 and
    universal classes;
  * at a world w, `□(φ ↔ 𝒜φ)` holds exactly when φ agrees with its
    actual value at every world accessible from w;
  * 𝒜 is inert for real-world validity, and general validity of 𝒜φ
    coincides with real-world validity of φ.

  These are the formal content of Zalta's claim that some logical
  truths are not necessary (Zalta 1988): if logical truth is
  real-world validity, `φ ↔ 𝒜φ` is a logical truth whose
  necessitation is not.

  Nothing here depends on the axioms of the development; the file
  uses only Lean's own logic.
-/

namespace ActualityLogic

/-- Formulas over a type α of atoms. -/
inductive Formula (α : Type) where
  | atom : α → Formula α
  | bot  : Formula α
  | neg  : Formula α → Formula α
  | conj : Formula α → Formula α → Formula α
  | impl : Formula α → Formula α → Formula α
  | box  : Formula α → Formula α
  | act  : Formula α → Formula α

namespace Formula

variable {α : Type}

/-- Material biconditional. -/
def iff (φ ψ : Formula α) : Formula α := conj (impl φ ψ) (impl ψ φ)

/-- Possibility, as the dual of necessity. -/
def dia (φ : Formula α) : Formula α := neg (box (neg φ))

end Formula

open Formula

/-- A Kripke model with a designated actual world. -/
structure Model (α : Type) where
  W      : Type
  R      : W → W → Prop
  actual : W
  val    : α → W → Prop

variable {α : Type}

/-- Truth of a formula at a world of a model.  𝒜φ is true at any
    world exactly when φ is true at the model's actual world. -/
def sat (M : Model α) : Formula α → M.W → Prop
  | atom a,   w => M.val a w
  | bot,      _ => False
  | neg φ,    w => ¬ sat M φ w
  | conj φ ψ, w => sat M φ w ∧ sat M ψ w
  | impl φ ψ, w => sat M φ w → sat M ψ w
  | box φ,    w => ∀ v, M.R w v → sat M φ v
  | act φ,    _ => sat M φ M.actual

/-- A class of models. -/
abbrev ModelClass (α : Type) := Model α → Prop

/-- Every model. -/
def AllModels : ModelClass α := fun _ => True

/-- Models whose accessibility relation is an equivalence relation. -/
def S5Models : ModelClass α := fun M => Equivalence M.R

/-- Models whose accessibility relation is universal. -/
def UniversalModels : ModelClass α := fun M => ∀ w v, M.R w v

/-- Real-world validity: truth at the actual world of every model in C. -/
def RWValid (C : ModelClass α) (φ : Formula α) : Prop :=
  ∀ M, C M → sat M φ M.actual

/-- General validity: truth at every world of every model in C. -/
def GValid (C : ModelClass α) (φ : Formula α) : Prop :=
  ∀ M, C M → ∀ w, sat M φ w

/-! ## Truth conditions of the derived connectives -/

theorem sat_iff (M : Model α) (φ ψ : Formula α) (w : M.W) :
    sat M (iff φ ψ) w ↔ (sat M φ w ↔ sat M ψ w) :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem sat_act (M : Model α) (φ : Formula α) (w : M.W) :
    sat M (act φ) w ↔ sat M φ M.actual :=
  Iff.rfl

/-! ## Closure properties -/

/-- General validity implies real-world validity. -/
theorem GValid.rwValid {C : ModelClass α} {φ : Formula α}
    (h : GValid C φ) : RWValid C φ :=
  fun M hM => h M hM M.actual

/-- Real-world validity is closed under modus ponens. -/
theorem RWValid.mp {C : ModelClass α} {φ ψ : Formula α}
    (hφψ : RWValid C (impl φ ψ)) (hφ : RWValid C φ) : RWValid C ψ :=
  fun M hM => hφψ M hM (hφ M hM)

/-- General validity is closed under modus ponens. -/
theorem GValid.mp {C : ModelClass α} {φ ψ : Formula α}
    (hφψ : GValid C (impl φ ψ)) (hφ : GValid C φ) : GValid C ψ :=
  fun M hM w => hφψ M hM w (hφ M hM w)

/-- General validity is closed under necessitation. -/
theorem GValid.nec {C : ModelClass α} {φ : Formula α}
    (h : GValid C φ) : GValid C (box φ) :=
  fun M hM _ v _ => h M hM v

/-! ## The actuality truth -/

/-- `φ ↔ 𝒜φ` is real-world valid, for every formula and every class. -/
theorem actuality_rwValid (C : ModelClass α) (φ : Formula α) :
    RWValid C (iff φ (act φ)) :=
  fun M _ => (sat_iff M φ (act φ) M.actual).mpr Iff.rfl

/-- At any world w, the necessitation of the actuality truth holds
    exactly when φ takes its actual value at every world accessible
    from w. -/
theorem sat_box_actuality (M : Model α) (φ : Formula α) (w : M.W) :
    sat M (box (iff φ (act φ))) w ↔
      ∀ v, M.R w v → (sat M φ v ↔ sat M φ M.actual) :=
  ⟨fun h v hv => (sat_iff M φ (act φ) v).mp (h v hv),
   fun h v hv => (sat_iff M φ (act φ) v).mpr (h v hv)⟩

/-- In a universal model, the necessitation of the actuality truth
    holds exactly when φ is non-contingent: true everywhere or false
    everywhere. -/
theorem sat_box_actuality_universal (M : Model α) (hU : UniversalModels M)
    (φ : Formula α) (w : M.W) :
    sat M (box (iff φ (act φ))) w ↔
      (∀ v, sat M φ v) ∨ (∀ v, ¬ sat M φ v) := by
  rw [sat_box_actuality]
  constructor
  · intro h
    rcases Classical.em (sat M φ M.actual) with ha | hna
    · exact Or.inl fun v => (h v (hU w v)).mpr ha
    · exact Or.inr fun v hv => hna ((h v (hU w v)).mp hv)
  · rintro (hall | hnone) v _
    · exact ⟨fun _ => hall M.actual, fun _ => hall v⟩
    · exact ⟨fun hv => absurd hv (hnone v), fun ha => absurd ha (hnone M.actual)⟩

/-! ## A two-world countermodel -/

/-- Two worlds, `true` (actual) and `false`, mutually accessible; every
    atom is true at `true` only. -/
def twoWorlds (α : Type) : Model α where
  W      := Bool
  R      := fun _ _ => True
  actual := true
  val    := fun _ w => w = true

theorem twoWorlds_universal : UniversalModels (twoWorlds α) :=
  fun _ _ => trivial

theorem twoWorlds_S5 : S5Models (twoWorlds α) :=
  ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

/-- At the non-actual world of the countermodel, an atom and its
    actualisation disagree. -/
theorem twoWorlds_actuality_fails (a : α) :
    ¬ sat (twoWorlds α) (iff (atom a) (act (atom a))) false := by
  intro h
  have h' := ((sat_iff (twoWorlds α) (atom a) (act (atom a)) false).mp h).mpr rfl
  exact Bool.noConfusion h'

/-- For any class containing the countermodel, the actuality truth is
    not generally valid. -/
theorem actuality_not_gValid {C : ModelClass α} (hC : C (twoWorlds α)) (a : α) :
    ¬ GValid C (iff (atom a) (act (atom a))) :=
  fun h => twoWorlds_actuality_fails a (h _ hC false)

/-- For any class containing the countermodel, the necessitation of
    the actuality truth is not even real-world valid. -/
theorem box_actuality_not_rwValid {C : ModelClass α} (hC : C (twoWorlds α)) (a : α) :
    ¬ RWValid C (box (iff (atom a) (act (atom a)))) :=
  fun h => twoWorlds_actuality_fails a (h _ hC false trivial)

/-- Real-world validity is not closed under necessitation. -/
theorem rwValid_not_closed_under_nec {C : ModelClass α} (hC : C (twoWorlds α)) (a : α) :
    ∃ φ : Formula α, RWValid C φ ∧ ¬ RWValid C (box φ) :=
  ⟨iff (atom a) (act (atom a)), actuality_rwValid C _, box_actuality_not_rwValid hC a⟩

/-- Real-world validity is strictly weaker than general validity. -/
theorem rwValid_strictly_weaker {C : ModelClass α} (hC : C (twoWorlds α)) (a : α) :
    (∀ φ, GValid C φ → RWValid C φ) ∧
    ∃ φ : Formula α, RWValid C φ ∧ ¬ GValid C φ :=
  ⟨fun _ => GValid.rwValid,
   ⟨iff (atom a) (act (atom a)), actuality_rwValid C _, actuality_not_gValid hC a⟩⟩

/-- Zalta's thesis, for S5: with an atom available, some real-world
    valid formula has a necessitation that is not real-world valid. -/
theorem contingent_logical_truth_S5 (a : α) :
    ∃ φ : Formula α, RWValid S5Models φ ∧ ¬ RWValid S5Models (box φ) :=
  rwValid_not_closed_under_nec twoWorlds_S5 a

/-! ## Actuality is inert for real-world validity -/

/-- 𝒜φ is real-world valid exactly when φ is. -/
theorem rwValid_act_iff (C : ModelClass α) (φ : Formula α) :
    RWValid C (act φ) ↔ RWValid C φ :=
  Iff.rfl

/-- 𝒜φ is generally valid exactly when φ is real-world valid. -/
theorem gValid_act_iff (C : ModelClass α) (φ : Formula α) :
    GValid C (act φ) ↔ RWValid C φ :=
  ⟨fun h M hM => h M hM M.actual, fun h M hM _ => h M hM⟩

/-- What is actual is necessarily actual, in every model. -/
theorem act_imp_box_act_gValid (φ : Formula α) :
    GValid AllModels (impl (act φ) (box (act φ))) :=
  fun _ _ _ h _ _ => h

end ActualityLogic
