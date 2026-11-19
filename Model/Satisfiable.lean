/-
  A MODEL OF THE AXIOMS

  This file builds a concrete structure in which every axiom of the
  development holds, and in which the theory is not degenerate: there
  are two distinct worlds, a contingent proposition, a partial
  situation strictly below a world, an impossible situation, and an
  ordinary object alongside abstract ones.

  The file imports nothing from the development.  Each primitive is
  given a concrete definition under its original name, each defined
  notion that occurs in an axiom is copied verbatim, and each axiom is
  restated verbatim as a theorem and proved.  `scripts/check_model.py`
  verifies that every axiom and copied definition in the development
  matches its counterpart here character for character (up to
  whitespace), so the model cannot silently drift from the axioms.

  Since every axiom is true in this structure, no contradiction is
  derivable from them: the axiom set is consistent relative to Lean's
  own logic.

  The structure:
  * `Val := Bool` indexes two valuations; `true` is the actual one.
  * A proposition is a set of valuations, so the connectives are
    Boolean operations and the propositional identities hold.
  * Properties are propositions and `VAC` is the identity, so every
    property is propositional.
  * Objects are either modal indices `idx v`, which are concrete and
    encode nothing (the ordinary objects), or abstract objects
    `abs S`, one for each set S of properties (the situations).
  * Situated truth is encoding, so `abs S ⊨ p` iff `p ∈ S`: partial
    in general.  Obtaining is evaluation at the index's valuation,
    with abstract objects evaluated at the actual valuation.
-/

namespace Model

/-! ## Primitive types -/

/-- Valuations.  `true` is the actual valuation. -/
abbrev Val := Bool

/-- A proposition is a set of valuations. -/
abbrev Propn : Type := Val → Prop

/-- Every property is propositional. -/
abbrev Property : Type := Propn

/-- Objects: modal indices (ordinary) and abstract objects, one per
    set of properties. -/
inductive World where
  | idx : Val → World
  | abs : (Property → Prop) → World

open World

/-! ## Primitive relations and operators -/

def VAC : Propn → Property := id

def Enc : World → Property → Prop
  | idx _, _ => False
  | abs S, F => S F

def Encp (x : World) (p : Propn) : Prop := Enc x (VAC p)

def Object (_ : World) : Prop := True

def Situation : World → Prop
  | idx _ => False
  | abs _ => True

def TrueIn (x : World) (p : Propn) : Prop := Encp x p

notation:30 x " ⊨ " p => TrueIn x p

def neg (p : Propn) : Propn := fun v => ¬ p v

def conj (p q : Propn) : Propn := fun v => p v ∧ q v

def disj (p q : Propn) : Propn := fun v => p v ∨ q v

def impl (p q : Propn) : Propn := fun v => p v → q v

def bic (p q : Propn) : Propn := conj (impl p q) (impl q p)

notation "¬ₚ" => neg
infixl:70 " ∧ₚ " => conj
infixl:65 " ∨ₚ " => disj
infixr:60 " →ₚ " => impl

def Obtains : World → Propn → Prop
  | idx v, p => p v
  | abs _, p => p true

def Concrete (_ : World) : World → Prop
  | idx _ => True
  | abs _ => False

def actualWorld : World := abs (fun F => F true)

def SitJoin (x y : World) : World := abs (fun F => Enc x F ∨ Enc y F)

def meet (x y : World) : World := abs (fun F => Enc x F ∧ Enc y F)

/-! ## Definitions copied verbatim from the development -/

def R (_ _ : World) : Prop := True

def Box (p : World → Prop) (w : World) : Prop :=
  ∀ v : World, R w v → p v

def Diamond (p : World → Prop) : World → Prop :=
  fun w => ¬ Box (fun v => ¬ p v) w

notation "□" => Box
notation "◊" => Diamond

def OrdinaryObject (x : World) : Prop :=
  ◊ (fun w => Concrete w x) x

def AbstractObject (x : World) : Prop :=
  ¬ ◊ (fun w => Concrete w x) x

notation "O!" => OrdinaryObject
notation "A!" => AbstractObject

def PartOf (x y : World) : Prop :=
  ∀ F : Property, Enc x F → Enc y F

notation:15 x " ⊴ " y => PartOf x y

def Agree (s s' : World) : Prop :=
  ∀ p : Propn, (s ⊨ p) ↔ (s' ⊨ p)

def ExtEq (s s' : World) : Prop :=
  Situation s ∧ Situation s' ∧ Agree s s'

def Actual (s : World) : Prop :=
  ∀ p : Propn, (s ⊨ p) → Obtains actualWorld p

def Possible (s : World) : Prop :=
  ◊ (fun v => ∀ p : Propn, (s ⊨ p) → Obtains v p) actualWorld

def Worldhood (s : World) : Prop :=
  Situation s ∧
  ◊ (fun v => ∀ p : Propn, (s ⊨ p) ↔ Obtains v p) actualWorld

def Maximal₁ (s : World) : Prop :=
  ∀ p : Propn, (s ⊨ p) ∨ (s ⊨ ¬ₚ p)

def Partial₁ (s : World) : Prop :=
  ∃ p : Propn, ¬ (s ⊨ p) ∧ ¬ (s ⊨ ¬ₚ p)

def Consistent (s : World) : Prop :=
  ¬ ∃ p : Propn, (s ⊨ p) ∧ (s ⊨ ¬ₚ p)

/-! ## Helper lemmas -/

theorem diamond_intro {p : World → Prop} {w : World} (v : World)
    (h : p v) : ◊ p w :=
  fun hbox => hbox v trivial h

theorem diamond_elim {p : World → Prop} {w : World}
    (h : ◊ p w) : ∃ v, p v :=
  Classical.byContradiction fun hne => h (fun v _ hpv => hne ⟨v, hpv⟩)

theorem idx_ordinary (b : Val) : O! (idx b) :=
  diamond_intro (idx b) trivial

theorem abs_abstract (S : Property → Prop) : A! (abs S) :=
  fun h => h (fun _ _ hc => hc)

theorem not_abstract_idx (b : Val) : ¬ A! (idx b) :=
  fun h => h (idx_ordinary b)

/-! ## The axioms, restated verbatim and proved -/

theorem Enc_VAC_complete :
  ∀ (s : World) (F : Property),
    Situation s → Enc s F → ∃ p : Propn, F = VAC p :=
  fun _ F _ _ => ⟨F, rfl⟩

theorem situation_is_object : ∀ s : World, Situation s → Object s :=
  fun _ _ => trivial

theorem bic_def :
  ∀ p q : Propn, bic p q = conj (impl p q) (impl q p) :=
  fun _ _ => rfl

theorem neg_neg :
  ∀ p : Propn, neg (neg p) = p :=
  fun _ => funext fun _ => propext
    ⟨fun h => Classical.byContradiction h, fun h hn => hn h⟩

theorem deMorgan_conj :
  ∀ p q : Propn, neg (conj p q) = disj (neg p) (neg q) :=
  fun p _ => funext fun v => propext
    ⟨fun h => (Classical.em (p v)).elim
        (fun hp => Or.inr fun hq => h ⟨hp, hq⟩) Or.inl,
     fun h ⟨hp, hq⟩ => h.elim (· hp) (· hq)⟩

theorem deMorgan_disj :
  ∀ p q : Propn, neg (disj p q) = conj (neg p) (neg q) :=
  fun _ _ => funext fun _ => propext
    ⟨fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩,
     fun ⟨hnp, hnq⟩ h => h.elim hnp hnq⟩

theorem impl_as_disj :
  ∀ p q : Propn, impl p q = disj (neg p) q :=
  fun p _ => funext fun v => propext
    ⟨fun h => (Classical.em (p v)).elim (fun hp => Or.inr (h hp)) Or.inl,
     fun h hp => h.elim (absurd hp) id⟩

theorem conj_comm :
  ∀ p q : Propn, conj p q = conj q p :=
  fun _ _ => funext fun _ => propext and_comm

theorem disj_comm :
  ∀ p q : Propn, disj p q = disj q p :=
  fun _ _ => funext fun _ => propext or_comm

theorem conj_assoc :
  ∀ p q r : Propn, conj (conj p q) r = conj p (conj q r) :=
  fun _ _ _ => funext fun _ => propext and_assoc

theorem disj_assoc :
  ∀ p q r : Propn, disj (disj p q) r = disj p (disj q r) :=
  fun _ _ _ => funext fun _ => propext or_assoc

theorem Encp_def :
  ∀ x : World, ∀ p : Propn,
    Object x →
      (Encp x p ↔
        ∃ F : Property, F = VAC p ∧ Enc x F) :=
  fun _ p _ => ⟨fun h => ⟨VAC p, rfl, h⟩, fun ⟨_, hF, h⟩ => by subst hF; exact h⟩

theorem TrueIn_def :
  ∀ x : World, ∀ p : Propn,
    Object x →
      ((x ⊨ p) ↔ Encp x p) :=
  fun _ _ _ => Iff.rfl

theorem Obtains_neg :
  ∀ (v : World) (p : Propn),
    Obtains v (¬ₚ p) ↔ ¬ Obtains v p := by
  intro v p; cases v <;> exact Iff.rfl

theorem Obtains_conj :
  ∀ (v : World) (p q : Propn),
    Obtains v (p ∧ₚ q) ↔ Obtains v p ∧ Obtains v q := by
  intro v p q; cases v <;> exact Iff.rfl

theorem Obtains_disj :
  ∀ (v : World) (p q : Propn),
    Obtains v (p ∨ₚ q) ↔ Obtains v p ∨ Obtains v q := by
  intro v p q; cases v <;> exact Iff.rfl

theorem Obtains_impl :
  ∀ (v : World) (p q : Propn),
    Obtains v (p →ₚ q) ↔ (Obtains v p → Obtains v q) := by
  intro v p q; cases v <;> exact Iff.rfl

theorem ordinary_no_encoding :
  ∀ x : World, O! x → □ (fun _ => ¬ ∃ F : Property, Enc x F) x := by
  intro x hx
  cases x with
  | idx _ => exact fun _ _ ⟨_, h⟩ => h
  | abs S => exact absurd hx (abs_abstract S)

theorem Comprehension :
  ∀ φ : Property → Prop,
    ∃ x : World,
      A! x ∧ ∀ F : Property, Enc x F ↔ φ F :=
  fun φ => ⟨abs φ, abs_abstract φ, fun _ => Iff.rfl⟩

theorem abstract_extensionality :
  ∀ x y : World,
    A! x → A! y → (∀ F : Property, Enc x F ↔ Enc y F) → x = y := by
  intro x y hx hy h
  cases x with
  | idx b => exact absurd hx (not_abstract_idx b)
  | abs S =>
    cases y with
    | idx b => exact absurd hy (not_abstract_idx b)
    | abs T => exact congrArg abs (funext fun F => propext (h F))

theorem SitJoin_situation : ∀ s s' : World,
    Situation s → Situation s' → Situation (SitJoin s s') :=
  fun _ _ _ _ => trivial

theorem SitJoin_left : ∀ s s' : World, (s ⊴ SitJoin s s') :=
  fun _ _ _ h => Or.inl h

theorem SitJoin_right : ∀ s s' : World, (s' ⊴ SitJoin s s') :=
  fun _ _ _ h => Or.inr h

theorem SitJoin_minimal : ∀ s s' u : World,
    (s ⊴ u) → (s' ⊴ u) → (SitJoin s s' ⊴ u) :=
  fun _ _ _ h₁ h₂ F h => h.elim (h₁ F) (h₂ F)

theorem situation_extensionality :
  ∀ s s' : World, ExtEq s s' → s = s' := by
  intro s s' ⟨hs, hs', h⟩
  cases s with
  | idx _ => exact hs.elim
  | abs S =>
    cases s' with
    | idx _ => exact hs'.elim
    | abs T => exact congrArg abs (funext fun F => propext (h F))

theorem meet_situation : ∀ s s' : World,
    Situation s → Situation s' → Situation (meet s s') :=
  fun _ _ _ _ => trivial

theorem TrueIn_meet :
  ∀ (s s' : World) (p : Propn),
    (meet s s' ⊨ p) ↔ ((s ⊨ p) ∧ (s' ⊨ p)) :=
  fun _ _ _ => Iff.rfl

theorem situation_closed_under_parthood :
  ∀ s x : World, Situation s → A! x → (x ⊴ s) → Situation x := by
  intro _ x _ hx _
  cases x with
  | idx b => exact absurd hx (not_abstract_idx b)
  | abs _ => trivial

theorem actualWorld_faithful :
  Situation actualWorld ∧ ∀ p : Propn, (actualWorld ⊨ p) ↔ Obtains actualWorld p :=
  ⟨trivial, fun _ => Iff.rfl⟩

/-! ## Non-degeneracy

  The model refutes each collapse found in earlier versions of the
  axioms: there is more than one world, there are propositions and
  some are contingent, situations can be partial and strictly smaller
  than worlds, possibility is a real constraint, and ordinary and
  abstract objects coexist.
-/

/-- The world that makes true exactly what holds at the non-actual
    valuation. -/
def otherWorld : World := abs (fun F => F false)

/-- A contingent proposition: true at the actual valuation only. -/
def contingentProp : Propn := fun b => b = true

/-- The situation that makes nothing true. -/
def emptySituation : World := abs (fun _ => False)

/-- The situation that makes everything true. -/
def trivialSituation : World := abs (fun _ => True)

theorem actualWorld_is_world : Worldhood actualWorld :=
  ⟨trivial, diamond_intro (idx true) fun _ => Iff.rfl⟩

theorem otherWorld_is_world : Worldhood otherWorld :=
  ⟨trivial, diamond_intro (idx false) fun _ => Iff.rfl⟩

theorem worlds_distinct : actualWorld ≠ otherWorld := by
  intro h
  have h' := congrFun (World.abs.inj h) contingentProp
  have : (true = true) = (false = true) := h'
  exact Bool.noConfusion (cast this rfl)

theorem contingent :
    ◊ (fun v => Obtains v contingentProp) actualWorld ∧
    ◊ (fun v => Obtains v (¬ₚ contingentProp)) actualWorld :=
  ⟨diamond_intro (idx true) rfl,
   diamond_intro (idx false) (fun h => Bool.noConfusion h)⟩

theorem emptySituation_partial : Partial₁ emptySituation :=
  ⟨contingentProp, id, id⟩

theorem emptySituation_strict_part :
    (emptySituation ⊴ actualWorld) ∧ emptySituation ≠ actualWorld := by
  refine ⟨fun _ h => h.elim, fun h => ?_⟩
  have h' := congrFun (World.abs.inj h) contingentProp
  have : False = (true = true) := h'
  exact cast this.symm rfl

theorem emptySituation_possible : Possible emptySituation :=
  diamond_intro (idx true) fun _ h => h.elim

theorem emptySituation_not_world : ¬ Worldhood emptySituation := by
  intro ⟨_, h⟩
  obtain ⟨v, hv⟩ := diamond_elim h
  cases v with
  | idx b =>
    cases b with
    | true  => exact (hv contingentProp).mpr rfl
    | false => exact (hv (¬ₚ contingentProp)).mpr (fun h => Bool.noConfusion h)
  | abs _ => exact (hv contingentProp).mpr rfl

theorem trivialSituation_impossible : ¬ Possible trivialSituation := by
  intro h
  obtain ⟨v, hv⟩ := diamond_elim h
  exact (Obtains_neg v contingentProp).mp
    (hv (¬ₚ contingentProp) trivial) (hv contingentProp trivial)

theorem ordinary_and_abstract_exist :
    O! (idx true) ∧ A! actualWorld :=
  ⟨idx_ordinary true, abs_abstract _⟩

/-- The model is non-degenerate. -/
theorem nondegenerate :
    (Worldhood actualWorld ∧ Worldhood otherWorld ∧ actualWorld ≠ otherWorld) ∧
    (Partial₁ emptySituation ∧ (emptySituation ⊴ actualWorld) ∧
      emptySituation ≠ actualWorld) ∧
    (Possible emptySituation ∧ ¬ Worldhood emptySituation) ∧
    ¬ Possible trivialSituation ∧
    (◊ (fun v => Obtains v contingentProp) actualWorld ∧
      ◊ (fun v => Obtains v (¬ₚ contingentProp)) actualWorld) ∧
    (O! (idx true) ∧ A! actualWorld) :=
  ⟨⟨actualWorld_is_world, otherWorld_is_world, worlds_distinct⟩,
   ⟨emptySituation_partial, emptySituation_strict_part.1,
     emptySituation_strict_part.2⟩,
   ⟨emptySituation_possible, emptySituation_not_world⟩,
   trivialSituation_impossible,
   contingent,
   ordinary_and_abstract_exist⟩

end Model
