/-
  THE THEORY AS A STRUCTURE

  `Spec.Theory` bundles the primitives of the development and its
  axioms.  Each field corresponds to exactly one `axiom` declaration in
  Grounding/, Modality/ and Situation/, under the same name and with
  the same statement.  The file imports nothing, and both sides of the
  consistency argument are checked against it by Lean:

  * `developmentTheory` (Situation/Specification.lean) fills every
    field with the axiom of the same name, so each axiom has exactly
    the statement of its field, and `#check_axioms_are_fields` fails
    the build if the development has an axiom that is not a field;
  * `Model.theory` (Model/Satisfiable.lean) fills every field from a
    concrete structure, using only Lean's own logic.

  Hence the axioms are true in a model, and no contradiction is
  derivable from them.

  The defined notions that the axioms and the results about the model
  mention are defined here once, over an arbitrary theory.  Both the
  development and the model prove, by `rfl`, that their own
  definitions coincide with these.
-/

namespace Spec

/-! ## Notions needed to state the axioms -/

/-- Universal accessibility. -/
def R {W : Type} (_ _ : W) : Prop := True

/-- Necessity over the universal relation. -/
def Box {W : Type} (p : W → Prop) (w : W) : Prop :=
  ∀ v : W, R w v → p v

/-- Possibility, the dual of necessity. -/
def Diamond {W : Type} (p : W → Prop) : W → Prop :=
  fun w => ¬ Box (fun v => ¬ p v) w

/-- Ordinary objects (O!): possibly concrete. -/
def OrdinaryObject {W : Type} (Concrete : W → W → Prop) (x : W) : Prop :=
  Diamond (fun w => Concrete w x) x

/-- Abstract objects (A!): not possibly concrete. -/
def AbstractObject {W : Type} (Concrete : W → W → Prop) (x : W) : Prop :=
  ¬ Diamond (fun w => Concrete w x) x

/-- Objects: ordinary or abstract. -/
def Object {W : Type} (Concrete : W → W → Prop) (x : W) : Prop :=
  OrdinaryObject Concrete x ∨ AbstractObject Concrete x

/-! ## The primitives and axioms -/

/-- The primitives and axioms of the development, one field for each
    `axiom` declaration. -/
structure Theory where
  World : Type
  Property : Type
  Propn : Type
  Enc : World → Property → Prop
  Encp : World → Propn → Prop
  VAC : Propn → Property
  Concrete : World → World → Prop
  neg : Propn → Propn
  conj : Propn → Propn → Propn
  disj : Propn → Propn → Propn
  impl : Propn → Propn → Propn
  bic : Propn → Propn → Propn
  bic_def : ∀ p q : Propn, bic p q = conj (impl p q) (impl q p)
  neg_neg : ∀ p : Propn, neg (neg p) = p
  deMorgan_conj : ∀ p q : Propn, neg (conj p q) = disj (neg p) (neg q)
  deMorgan_disj : ∀ p q : Propn, neg (disj p q) = conj (neg p) (neg q)
  impl_as_disj : ∀ p q : Propn, impl p q = disj (neg p) q
  conj_comm : ∀ p q : Propn, conj p q = conj q p
  disj_comm : ∀ p q : Propn, disj p q = disj q p
  conj_assoc : ∀ p q r : Propn, conj (conj p q) r = conj p (conj q r)
  disj_assoc : ∀ p q r : Propn, disj (disj p q) r = disj p (disj q r)
  TrueIn : World → Propn → Prop
  Encp_def : ∀ x : World, ∀ p : Propn,
    Object Concrete x → (Encp x p ↔ ∃ F : Property, F = VAC p ∧ Enc x F)
  TrueIn_def : ∀ x : World, ∀ p : Propn,
    Object Concrete x → (TrueIn x p ↔ Encp x p)
  Obtains : World → Propn → Prop
  Obtains_neg : ∀ (v : World) (p : Propn), Obtains v (neg p) ↔ ¬ Obtains v p
  Obtains_conj : ∀ (v : World) (p q : Propn),
    Obtains v (conj p q) ↔ Obtains v p ∧ Obtains v q
  Obtains_disj : ∀ (v : World) (p q : Propn),
    Obtains v (disj p q) ↔ Obtains v p ∨ Obtains v q
  Obtains_impl : ∀ (v : World) (p q : Propn),
    Obtains v (impl p q) ↔ (Obtains v p → Obtains v q)
  VAC_congr : ∀ (p q : Propn), VAC p = VAC q →
    ∀ v : World, Obtains v p ↔ Obtains v q
  ordinary_no_encoding : ∀ x : World,
    OrdinaryObject Concrete x → Box (fun _ => ¬ ∃ F : Property, Enc x F) x
  Comprehension : ∀ φ : Property → Prop,
    ∃ x : World, AbstractObject Concrete x ∧ ∀ F : Property, Enc x F ↔ φ F
  abstract_extensionality : ∀ x y : World,
    AbstractObject Concrete x → AbstractObject Concrete y →
      (∀ F : Property, Enc x F ↔ Enc y F) → x = y
  actualIndex : World

namespace Theory

variable (T : Theory)

/-! ## Defined notions, over an arbitrary theory -/

/-- Situations: abstract objects encoding only propositional properties. -/
def Situation (x : T.World) : Prop :=
  AbstractObject T.Concrete x ∧ ∀ F : T.Property, T.Enc x F → ∃ p : T.Propn, F = T.VAC p

/-- Parthood. -/
def PartOf (x y : T.World) : Prop :=
  ∀ F : T.Property, T.Enc x F → T.Enc y F

/-- Agreement on situated truth. -/
def Agree (s s' : T.World) : Prop :=
  ∀ p : T.Propn, T.TrueIn s p ↔ T.TrueIn s' p

/-- Extensional equivalence of situations. -/
def ExtEq (s s' : T.World) : Prop :=
  T.Situation s ∧ T.Situation s' ∧ T.Agree s s'

/-- The actual world, by comprehension. -/
noncomputable def actualWorld : T.World :=
  Classical.choose (T.Comprehension
    (fun F => ∃ p : T.Propn, F = T.VAC p ∧ T.Obtains T.actualIndex p))

/-- Actuality of a situation. -/
def Actual (s : T.World) : Prop :=
  ∀ p : T.Propn, T.TrueIn s p → T.Obtains T.actualIndex p

/-- Possibility of a situation. -/
def Possible (s : T.World) : Prop :=
  Diamond (fun v => ∀ p : T.Propn, T.TrueIn s p → T.Obtains v p) T.actualIndex

/-- Worldhood. -/
def Worldhood (s : T.World) : Prop :=
  T.Situation s ∧
  Diamond (fun v => ∀ p : T.Propn, T.TrueIn s p ↔ T.Obtains v p) T.actualIndex

/-- Maximality (first sense). -/
def Maximal₁ (s : T.World) : Prop :=
  ∀ p : T.Propn, T.TrueIn s p ∨ T.TrueIn s (T.neg p)

/-- Partiality (first sense). -/
def Partial₁ (s : T.World) : Prop :=
  ∃ p : T.Propn, ¬ T.TrueIn s p ∧ ¬ T.TrueIn s (T.neg p)

/-- Consistency. -/
def Consistent (s : T.World) : Prop :=
  ¬ ∃ p : T.Propn, T.TrueIn s p ∧ T.TrueIn s (T.neg p)

/-- The actuality operator. -/
def Actually (p : T.World → Prop) : T.World → Prop :=
  fun _ => p T.actualIndex

/-- Actualist quantification over the concrete objects at an index. -/
def AllConcrete (φ : T.World → T.World → Prop) : T.World → Prop :=
  fun v => ∀ x : T.World, T.Concrete v x → φ x v

/-- Everything concrete is actually concrete. -/
def EverythingActuallyConcrete : T.World → Prop :=
  T.AllConcrete (fun x => T.Actually (fun v => T.Concrete v x))

/-- The Barcan formula for the actualist quantifier. -/
def Barcan (φ : T.World → T.World → Prop) : T.World → Prop :=
  fun w => (∀ x : T.World, T.Concrete w x → Box (φ x) w) → Box (T.AllConcrete φ) w

/-- The converse Barcan formula for the actualist quantifier. -/
def ConverseBarcan (φ : T.World → T.World → Prop) : T.World → Prop :=
  fun w => Box (T.AllConcrete φ) w → ∀ x : T.World, T.Concrete w x → Box (φ x) w

end Theory

end Spec
