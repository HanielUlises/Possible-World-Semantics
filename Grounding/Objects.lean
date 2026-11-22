import Grounding.Ontology
import Modality.Operators

/-
  OBJECTS AND SITUATIONS

  Concreteness is a primitive modal predicate.  Ordinariness and
  abstractness are defined from it via possibility and its negation,
  and objecthood and situationhood are defined from those, as in
  Zalta's abstract object theory:

    Object(x)     :=  O!x ∨ A!x
    Situation(x)  :=  A!x ∧ ∀F (xF → ∃p (F = [λy p]))

  so a situation is an abstract object that encodes only propositional
  properties.  That situations are objects, and that they encode only
  properties of the form `VAC p`, are then theorems rather than
  postulates.
-/

-- §1  Primitives

/--
  Concreteness predicate (existence predicate, E!).

  `Concrete w x` holds when x is spatiotemporally located at world w.
  Concreteness is world-relative: an object may be concrete at some
  worlds and not others.
-/
axiom Concrete : World → World → Prop

-- §2  Ordinary and abstract objects

/--
  Ordinary object (O!).

  x is ordinary iff it is possibly concrete — there exists some world
  at which x is spatiotemporally located.
-/
def OrdinaryObject (x : World) : Prop :=
  ◊ (fun w => Concrete w x) x

/--
  Abstract object (A!).

  x is abstract iff it is not possibly concrete — it is necessarily
  non-concrete.  This is the negation of ordinariness rather than an
  independent primitive.
-/
def AbstractObject (x : World) : Prop :=
  ¬ ◊ (fun w => Concrete w x) x

-- Convenient notations
notation "O!" => OrdinaryObject
notation "A!" => AbstractObject

-- §3  Objects and situations

/--
  Objecthood: an object is ordinary or abstract.
-/
def Object (x : World) : Prop :=
  O! x ∨ A! x

/--
  Situationhood (Zalta 1993): a situation is an abstract object that
  encodes only propositional properties, those of the form `VAC p`.
-/
def Situation (x : World) : Prop :=
  A! x ∧ ∀ F : Property, Enc x F → ∃ p : Propn, F = VAC p

/-- Everything is an object: abstractness is non-ordinariness. -/
theorem object_total (x : World) : Object x :=
  (Classical.em (O! x)).elim Or.inl Or.inr

/-- Situations are abstract objects. -/
theorem situation_abstract (s : World) (hs : Situation s) : A! s :=
  hs.1

/-- Every situation is an object (formerly postulated; OP-3). -/
theorem situation_is_object : ∀ s : World, Situation s → Object s :=
  fun _ hs => Or.inr hs.1

/-- Every property encoded by a situation is the vacuous abstraction
    of some proposition (formerly postulated). -/
theorem Enc_VAC_complete :
    ∀ (s : World) (F : Property),
      Situation s → Enc s F → ∃ p : Propn, F = VAC p :=
  fun _ F hs hF => hs.2 F hF
