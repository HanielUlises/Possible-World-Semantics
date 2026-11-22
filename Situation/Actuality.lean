import Modality.Operators
import Modality.ActualityLogic
import Situation.Definitions
import Situation.Theorems

/-
  ACTUALITY AND CONTINGENT LOGICAL TRUTH

  The actuality operator 𝒜 evaluates a condition at the actual index,
  whatever the index of evaluation.  It is defined, not
  postulated: no axiom is added.

  The central facts:

  * `actuality_truth`: p ↔ 𝒜p holds at the actual index, for every p,
    by definition alone.  It is a logical truth in the real-world sense.
  * `box_actuality_truth_iff`: its necessitation holds exactly when p
    is non-contingent, so `contingent_actuality_truth_not_necessary`:
    for a contingent p, the logical truth p ↔ 𝒜p is not necessary.
  * The theory itself does not settle whether anything is contingent.
    `Model/Satisfiable.lean` exhibits a model of all the axioms in
    which a proposition is contingent, so there the necessitation
    fails.
  * `theoryModel` reads the development as a model of the deep
    embedding in Modality/ActualityLogic.lean, and `sat_theoryModel`
    shows that the two treatments of 𝒜 agree.
-/

/-- The actuality operator: 𝒜 p holds at any index iff p holds at the
    actual index. -/
def Actually (p : World → Prop) : World → Prop :=
  fun _ => p actualIndex

notation "𝒜" => Actually

/-- At the actual index, 𝒜 p is just p. -/
theorem actually_at_actual (p : World → Prop) :
    𝒜 p actualIndex ↔ p actualIndex :=
  Iff.rfl

/-- The actuality truth: p ↔ 𝒜p holds at the actual index, for every p. -/
theorem actuality_truth (p : World → Prop) :
    (fun w => p w ↔ 𝒜 p w) actualIndex :=
  Iff.rfl

/-- 𝒜 is rigid: its value does not depend on the index. -/
theorem actually_rigid (p : World → Prop) (w v : World) :
    𝒜 p w ↔ 𝒜 p v :=
  Iff.rfl

/-- 𝒜 is idempotent. -/
theorem actually_actually (p : World → Prop) (w : World) :
    𝒜 (𝒜 p) w ↔ 𝒜 p w :=
  Iff.rfl

/-- What is actual is necessarily actual, and conversely. -/
theorem box_actually (p : World → Prop) (w : World) :
    □ (𝒜 p) w ↔ 𝒜 p w :=
  ⟨fun h => h w (R_refl w), fun h _ _ => h⟩

/-- What is possibly actual is actual. -/
theorem diamond_actually (p : World → Prop) (w : World) :
    ◊ (𝒜 p) w ↔ 𝒜 p w := by
  rw [Diamond_iff_exists]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨w, R_refl w, h⟩⟩

/-- The necessitation of the actuality truth holds exactly when p is
    non-contingent: necessary or impossible. -/
theorem box_actuality_truth_iff (p : World → Prop) (w : World) :
    □ (fun v => p v ↔ 𝒜 p v) w ↔ (Necessary p w ∨ Impossible p w) := by
  constructor
  · intro h
    rcases Classical.em (p actualIndex) with ha | hna
    · exact Or.inl fun v hv => (h v hv).mpr ha
    · exact Or.inr fun v hv hpv => hna ((h v hv).mp hpv)
  · rintro (hnec | himp) v hv
    · exact ⟨fun _ => hnec actualIndex trivial, fun _ => hnec v hv⟩
    · exact ⟨fun hpv => absurd hpv (himp v hv),
             fun ha => absurd ha (himp actualIndex trivial)⟩

/-- A contingent logical truth: for contingent p, the actuality truth
    p ↔ 𝒜p, which holds at the actual index for every p, is not
    necessary. -/
theorem contingent_actuality_truth_not_necessary (p : World → Prop) (w : World)
    (hc : Contingent p w) :
    ¬ □ (fun v => p v ↔ 𝒜 p v) w := by
  rw [box_actuality_truth_iff]
  rintro (hnec | himp)
  · exact contingent_not_necessary p w hc hnec
  · exact (Box_iff_not_Diamond_not _ w).mp himp
      (Diamond_monotone p _ w (fun _ hp hnp => hnp hp) hc.1)

/-- The actuality truth for a proposition: q obtains iff it actually
    obtains, at the actual index. -/
theorem obtains_actuality_truth (q : Propn) :
    (fun w => Obtains w q ↔ 𝒜 (fun v => Obtains v q) w) actualIndex :=
  Iff.rfl

/-- If a proposition's obtaining is contingent, the actuality truth
    for it is not necessary. -/
theorem obtains_actuality_truth_not_necessary (q : Propn)
    (hc : Contingent (fun v => Obtains v q) actualIndex) :
    ¬ □ (fun w => Obtains w q ↔ 𝒜 (fun v => Obtains v q) w) actualIndex :=
  contingent_actuality_truth_not_necessary _ actualIndex hc

/-- Actuality of a situation is the actualisation of its possibility
    condition: s is actual iff, actually, everything true in s obtains. -/
theorem actual_iff_actually (s : World) (w : World) :
    Actual s ↔ 𝒜 (fun v => ∀ p : Propn, (s ⊨ p) → Obtains v p) w :=
  Iff.rfl

/-! ## The development as a model of the logic of actuality -/

open ActualityLogic in
/-- The development read as a model of the deep embedding: indices are
    worlds, accessibility is R, the designated actual world is `actualIndex`, and
    an atom is a proposition, true where it obtains. -/
noncomputable def theoryModel : ActualityLogic.Model Propn where
  W      := World
  R      := R
  actual := actualIndex
  val    := fun q v => Obtains v q

open ActualityLogic in
/-- Translation of formulas into conditions on worlds. -/
def interp : ActualityLogic.Formula Propn → World → Prop
  | .atom q,   v => Obtains v q
  | .bot,      _ => False
  | .neg φ,    v => ¬ interp φ v
  | .conj φ ψ, v => interp φ v ∧ interp ψ v
  | .impl φ ψ, v => interp φ v → interp ψ v
  | .box φ,    v => □ (interp φ) v
  | .act φ,    v => 𝒜 (interp φ) v

open ActualityLogic in
/-- The deep and shallow treatments agree: truth in `theoryModel` is
    the shallow interpretation, with 𝒜 as `Actually` and □ as `Box`. -/
theorem sat_theoryModel (φ : ActualityLogic.Formula Propn) (v : World) :
    ActualityLogic.sat theoryModel φ v ↔ interp φ v := by
  induction φ generalizing v with
  | atom q => exact Iff.rfl
  | bot => exact Iff.rfl
  | neg φ ih => exact not_congr (ih v)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ v) (ihψ v)
  | impl φ ψ ihφ ihψ => exact imp_congr (ihφ v) (ihψ v)
  | box φ ih => exact forall_congr' fun u => imp_congr Iff.rfl (ih u)
  | act φ ih => exact ih actualIndex

open ActualityLogic in
/-- The development's model is universal, hence in every class the
    metatheorems of Modality/ActualityLogic.lean quantify over. -/
theorem theoryModel_universal : UniversalModels theoryModel :=
  fun _ _ => trivial

open ActualityLogic in
/-- Every real-world valid formula over universal models holds at the
    actual index of the development. -/
theorem rwValid_holds_actually (φ : ActualityLogic.Formula Propn)
    (h : RWValid UniversalModels φ) : interp φ actualIndex :=
  (sat_theoryModel φ actualIndex).mp (h theoryModel theoryModel_universal)
