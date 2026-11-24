/-
  A MODEL OF THE AXIOMS

  This file builds a concrete structure in which every axiom of the
  development holds, and in which the theory is not degenerate: there
  are two distinct worlds, a contingent proposition, a partial
  situation strictly below a world, an impossible situation, and an
  ordinary object alongside abstract ones, and an object that could
  have been concrete without actually being so.  Propositions are
  hyperintensional: there are distinct but necessarily equivalent
  propositions, and a situation that makes one true but not the other.

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
  * A proposition is a set of valuations together with a tag bit.
    The connectives are Boolean operations on the sets and join the
    tags, so the propositional identities hold; obtaining ignores the
    tag, so propositions that differ only in their tag are distinct but
    necessarily equivalent (`hyperintensional`).
  * Properties are propositions and `VAC` is the identity, so every
    property is propositional.
  * Objects are either modal indices `idx v`, which encode nothing
    (the ordinary objects), or abstract objects `abs S`, one for each
    set S of properties (the situations).  Abstract objects are
    concrete nowhere.  At the actual index only `idx true` is
    concrete; at the non-actual index both indices are, so the domain
    of concrete objects grows (`growing_domain`).
  * Situated truth is encoding, so `abs S ⊨ p` iff `p ∈ S`: partial
    in general.  Obtaining is evaluation at the index's valuation,
    with abstract objects evaluated at the actual valuation.
  * The actual index is `idx true`.  The actual world is defined, as in
    the development, by comprehension; it is the abstract object that
    encodes what holds at the actual valuation (`actualWorld_eq`).
-/

namespace Model

/-! ## Primitive types -/

/-- Valuations.  `true` is the actual valuation. -/
abbrev Val := Bool

/-- A proposition is a set of valuations together with a tag.  The
    tag plays no role in obtaining, so propositions that differ only
    in their tag are necessarily equivalent but distinct. -/
structure Propn where
  holds : Val → Prop
  tag   : Bool

/-- Propositions with the same valuations and the same tag are equal. -/
theorem Propn.ext' {p q : Propn} (h₁ : p.holds = q.holds) (h₂ : p.tag = q.tag) :
    p = q := by
  cases p; cases q; cases h₁; cases h₂; rfl

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

def TrueIn (x : World) (p : Propn) : Prop := Encp x p

notation:30 x " ⊨ " p => TrueIn x p

def neg (p : Propn) : Propn := ⟨fun v => ¬ p.holds v, p.tag⟩

def conj (p q : Propn) : Propn := ⟨fun v => p.holds v ∧ q.holds v, p.tag || q.tag⟩

def disj (p q : Propn) : Propn := ⟨fun v => p.holds v ∨ q.holds v, p.tag || q.tag⟩

def impl (p q : Propn) : Propn := disj (neg p) q

def bic (p q : Propn) : Propn := conj (impl p q) (impl q p)

notation "¬ₚ" => neg
infixl:70 " ∧ₚ " => conj
infixl:65 " ∨ₚ " => disj
infixr:60 " →ₚ " => impl

def Obtains : World → Propn → Prop
  | idx v, p => p.holds v
  | abs _, p => p.holds true

def Concrete (w : World) : World → Prop
  | idx b => w = idx false ∨ b = true
  | abs _ => False

def actualIndex : World := idx true


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

def Object (x : World) : Prop :=
  O! x ∨ A! x

def Situation (x : World) : Prop :=
  A! x ∧ ∀ F : Property, Enc x F → ∃ p : Propn, F = VAC p

def PartOf (x y : World) : Prop :=
  ∀ F : Property, Enc x F → Enc y F

notation:15 x " ⊴ " y => PartOf x y

def Agree (s s' : World) : Prop :=
  ∀ p : Propn, (s ⊨ p) ↔ (s' ⊨ p)

def ExtEq (s s' : World) : Prop :=
  Situation s ∧ Situation s' ∧ Agree s s'

def Actual (s : World) : Prop :=
  ∀ p : Propn, (s ⊨ p) → Obtains actualIndex p

def Possible (s : World) : Prop :=
  ◊ (fun v => ∀ p : Propn, (s ⊨ p) → Obtains v p) actualIndex

def Worldhood (s : World) : Prop :=
  Situation s ∧
  ◊ (fun v => ∀ p : Propn, (s ⊨ p) ↔ Obtains v p) actualIndex

def Maximal₁ (s : World) : Prop :=
  ∀ p : Propn, (s ⊨ p) ∨ (s ⊨ ¬ₚ p)

def Partial₁ (s : World) : Prop :=
  ∃ p : Propn, ¬ (s ⊨ p) ∧ ¬ (s ⊨ ¬ₚ p)

def Consistent (s : World) : Prop :=
  ¬ ∃ p : Propn, (s ⊨ p) ∧ (s ⊨ ¬ₚ p)

def Actually (p : World → Prop) : World → Prop :=
  fun _ => p actualIndex

notation "𝒜" => Actually

def AllConcrete (φ : World → World → Prop) : World → Prop :=
  fun v => ∀ x : World, Concrete v x → φ x v

def EverythingActuallyConcrete : World → Prop :=
  AllConcrete (fun x => 𝒜 (fun v => Concrete v x))

def Barcan (φ : World → World → Prop) : World → Prop :=
  fun w => (∀ x : World, Concrete w x → □ (φ x) w) → □ (AllConcrete φ) w

def ConverseBarcan (φ : World → World → Prop) : World → Prop :=
  fun w => □ (AllConcrete φ) w → ∀ x : World, Concrete w x → □ (φ x) w

/-! ## Helper lemmas -/

theorem diamond_intro {p : World → Prop} {w : World} (v : World)
    (h : p v) : ◊ p w :=
  fun hbox => hbox v trivial h

theorem diamond_elim {p : World → Prop} {w : World}
    (h : ◊ p w) : ∃ v, p v :=
  Classical.byContradiction fun hne => h (fun v _ hpv => hne ⟨v, hpv⟩)

theorem idx_ordinary (b : Val) : O! (idx b) :=
  diamond_intro (idx false) (Or.inl rfl)

theorem abs_abstract (S : Property → Prop) : A! (abs S) :=
  fun h => h (fun _ _ hc => hc)

theorem not_abstract_idx (b : Val) : ¬ A! (idx b) :=
  fun h => h (idx_ordinary b)

theorem abs_situation (S : Property → Prop) : Situation (abs S) :=
  ⟨abs_abstract S, fun F _ => ⟨F, rfl⟩⟩

/-! ## The axioms, restated verbatim and proved -/

theorem bic_def :
  ∀ p q : Propn, bic p q = conj (impl p q) (impl q p) :=
  fun _ _ => rfl

theorem neg_neg :
  ∀ p : Propn, neg (neg p) = p :=
  fun _ => Propn.ext' (funext fun _ => propext
    ⟨fun h => Classical.byContradiction h, fun h hn => hn h⟩) rfl

theorem deMorgan_conj :
  ∀ p q : Propn, neg (conj p q) = disj (neg p) (neg q) :=
  fun p _ => Propn.ext' (funext fun v => propext
    ⟨fun h => (Classical.em (p.holds v)).elim
        (fun hp => Or.inr fun hq => h ⟨hp, hq⟩) Or.inl,
     fun h ⟨hp, hq⟩ => h.elim (· hp) (· hq)⟩) rfl

theorem deMorgan_disj :
  ∀ p q : Propn, neg (disj p q) = conj (neg p) (neg q) :=
  fun _ _ => Propn.ext' (funext fun _ => propext
    ⟨fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩,
     fun ⟨hnp, hnq⟩ h => h.elim hnp hnq⟩) rfl

theorem impl_as_disj :
  ∀ p q : Propn, impl p q = disj (neg p) q :=
  fun _ _ => rfl

theorem conj_comm :
  ∀ p q : Propn, conj p q = conj q p :=
  fun _ _ => Propn.ext' (funext fun _ => propext and_comm) (Bool.or_comm _ _)

theorem disj_comm :
  ∀ p q : Propn, disj p q = disj q p :=
  fun _ _ => Propn.ext' (funext fun _ => propext or_comm) (Bool.or_comm _ _)

theorem conj_assoc :
  ∀ p q r : Propn, conj (conj p q) r = conj p (conj q r) :=
  fun _ _ _ => Propn.ext' (funext fun _ => propext and_assoc) (Bool.or_assoc _ _ _)

theorem disj_assoc :
  ∀ p q r : Propn, disj (disj p q) r = disj p (disj q r) :=
  fun _ _ _ => Propn.ext' (funext fun _ => propext or_assoc) (Bool.or_assoc _ _ _)

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
  intro v p q
  cases v <;>
    exact ⟨fun h hp => h.elim (absurd hp) id,
      fun h => (Classical.em _).elim (fun hp => Or.inr (h hp)) Or.inl⟩

theorem VAC_congr :
  ∀ (p q : Propn), VAC p = VAC q →
    ∀ v : World, Obtains v p ↔ Obtains v q :=
  fun _ _ h _ => by simp only [VAC, id] at h; subst h; exact Iff.rfl

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

noncomputable def actualWorld : World :=
  Classical.choose (Comprehension (fun F => ∃ p : Propn, F = VAC p ∧ Obtains actualIndex p))

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

/-! ## Non-degeneracy

  The model refutes each collapse found in earlier versions of the
  axioms: there is more than one world, there are propositions and
  some are contingent, situations can be partial and strictly smaller
  than worlds, possibility is a real constraint, and ordinary and
  abstract objects coexist.
-/

/-- The actual world is the abstract object encoding what holds at the
    actual valuation. -/
theorem actualWorld_eq : actualWorld = abs (fun F => F.holds true) := by
  have spec := Classical.choose_spec
    (Comprehension (fun F => ∃ p : Propn, F = VAC p ∧ Obtains actualIndex p))
  apply abstract_extensionality _ _ spec.1 (abs_abstract _)
  intro F
  refine (spec.2 F).trans ⟨fun ⟨p, hp, hob⟩ => ?_, fun h => ⟨F, rfl, h⟩⟩
  subst hp
  exact hob

/-- The world that makes true exactly what holds at the non-actual
    valuation. -/
def otherWorld : World := abs (fun F => F.holds false)

/-- A contingent proposition: true at the actual valuation only. -/
def contingentProp : Propn := ⟨fun b => b = true, false⟩

/-- The situation that makes nothing true. -/
def emptySituation : World := abs (fun _ => False)

/-- The situation that makes everything true. -/
def trivialSituation : World := abs (fun _ => True)

theorem actualWorld_is_world : Worldhood actualWorld := by
  rw [actualWorld_eq]
  exact ⟨abs_situation _, diamond_intro (idx true) fun _ => Iff.rfl⟩

theorem otherWorld_is_world : Worldhood otherWorld :=
  ⟨abs_situation _, diamond_intro (idx false) fun _ => Iff.rfl⟩

theorem worlds_distinct : actualWorld ≠ otherWorld := by
  rw [actualWorld_eq]
  intro h
  have h' := congrFun (World.abs.inj h) contingentProp
  have : (true = true) = (false = true) := h'
  exact Bool.noConfusion (cast this rfl)

theorem contingent :
    ◊ (fun v => Obtains v contingentProp) actualIndex ∧
    ◊ (fun v => Obtains v (¬ₚ contingentProp)) actualIndex :=
  ⟨diamond_intro (idx true) rfl,
   diamond_intro (idx false) (fun h => Bool.noConfusion h)⟩

theorem emptySituation_partial : Partial₁ emptySituation :=
  ⟨contingentProp, id, id⟩

theorem emptySituation_strict_part :
    (emptySituation ⊴ actualWorld) ∧ emptySituation ≠ actualWorld := by
  rw [actualWorld_eq]
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
  ⟨idx_ordinary true, actualWorld_eq ▸ abs_abstract _⟩

/-- A contingent logical truth in a model of the whole theory: the
    actuality truth for `contingentProp` holds at the actual world, as
    it does for every proposition, but its necessitation fails, since
    at the non-actual index the proposition does not obtain while it
    actually does. -/
theorem contingent_logical_truth :
    (fun w => Obtains w contingentProp ↔
      𝒜 (fun v => Obtains v contingentProp) w) actualIndex ∧
    ¬ □ (fun w => Obtains w contingentProp ↔
      𝒜 (fun v => Obtains v contingentProp) w) actualIndex :=
  ⟨Iff.rfl, fun h => Bool.noConfusion ((h (idx false) trivial).mpr rfl)⟩

/-- The domain of concrete objects varies: `idx false` is concrete at
    the non-actual index but not at the actual one. -/
theorem growing_domain :
    Concrete (idx false) (idx false) ∧ ¬ Concrete actualIndex (idx false) :=
  ⟨Or.inl rfl, fun h => h.elim (fun h' => Bool.noConfusion (World.idx.inj h'))
    (fun h' => Bool.noConfusion h')⟩

/-- A quantified contingent logical truth in a model of the whole
    theory: everything concrete is actually concrete at the actual
    index, as it is in every model, but not necessarily, since
    `idx false` could have been concrete without actually being so. -/
theorem quantified_contingent_logical_truth :
    EverythingActuallyConcrete actualIndex ∧
    ¬ □ EverythingActuallyConcrete actualIndex :=
  ⟨fun _ h => h,
   fun h => growing_domain.2 (h (idx false) trivial (idx false) growing_domain.1)⟩

/-- The Barcan formula fails at the actual index: everything actually
    concrete is necessarily actually concrete, but `idx false` could
    be concrete without being actually concrete. -/
theorem barcan_fails :
    ¬ Barcan (fun x _ => Concrete actualIndex x) actualIndex :=
  fun h => growing_domain.2
    (h (fun _ hx _ _ => hx) (idx false) trivial (idx false) growing_domain.1)

/-- The converse Barcan formula fails at the non-actual index: necessarily
    everything concrete is concrete, but `idx false`, concrete there, is
    not concrete at the actual index. -/
theorem converseBarcan_fails :
    ¬ ConverseBarcan (fun x v => Concrete v x) (idx false) :=
  fun h => growing_domain.2
    (h (fun _ _ _ hx => hx) (idx false) growing_domain.1 actualIndex trivial)

/-- A proposition necessarily equivalent to `contingentProp` but
    distinct from it. -/
def variantProp : Propn := ⟨fun b => b = true, true⟩

/-- The situation that makes `contingentProp` true and nothing else. -/
def singletonSituation : World := abs (fun F => F = contingentProp)

/-- Propositions are hyperintensional: `contingentProp` and
    `variantProp` are distinct but necessarily equivalent, and a
    possible situation makes the first true but not the second. -/
theorem hyperintensional :
    contingentProp ≠ variantProp ∧
    □ (fun v => Obtains v contingentProp ↔ Obtains v variantProp) actualIndex ∧
    Situation singletonSituation ∧ Possible singletonSituation ∧
    (singletonSituation ⊨ contingentProp) ∧ ¬ (singletonSituation ⊨ variantProp) :=
  ⟨fun h => Bool.noConfusion (congrArg Propn.tag h),
   fun v _ => by cases v <;> exact Iff.rfl,
   abs_situation _,
   diamond_intro (idx true) fun _ h => by
     have h' : _ = contingentProp := h
     subst h'; rfl,
   rfl,
   fun h => Bool.noConfusion (congrArg Propn.tag h)⟩

/-- The model is non-degenerate. -/
theorem nondegenerate :
    (Worldhood actualWorld ∧ Worldhood otherWorld ∧ actualWorld ≠ otherWorld) ∧
    (Partial₁ emptySituation ∧ (emptySituation ⊴ actualWorld) ∧
      emptySituation ≠ actualWorld) ∧
    (Possible emptySituation ∧ ¬ Worldhood emptySituation) ∧
    ¬ Possible trivialSituation ∧
    (◊ (fun v => Obtains v contingentProp) actualIndex ∧
      ◊ (fun v => Obtains v (¬ₚ contingentProp)) actualIndex) ∧
    (O! (idx true) ∧ A! actualWorld) :=
  ⟨⟨actualWorld_is_world, otherWorld_is_world, worlds_distinct⟩,
   ⟨emptySituation_partial, emptySituation_strict_part.1,
     emptySituation_strict_part.2⟩,
   ⟨emptySituation_possible, emptySituation_not_world⟩,
   trivialSituation_impossible,
   contingent,
   ordinary_and_abstract_exist⟩

end Model
