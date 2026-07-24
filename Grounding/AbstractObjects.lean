import Grounding.Ontology
import Grounding.Truth
import Modality.Operators

/-
  ABSTRACT AND ORDINARY OBJECTS

  This file introduces the concrete/abstract distinction following
  Zalta's abstract object theory.  Concreteness is a primitive modal
  predicate; ordinariness and abstractness are defined from it via
  possibility and its negation.

  The comprehension principle for abstract objects is postulated as an
  axiom: for every property-predicate φ there exists an abstract object
  that encodes exactly the properties satisfying φ.  Together with the
  constraint that ordinary objects cannot encode properties, this gives
  a clean two-sorted ontology within the single `World` type.
-/

-- §1  Primitives
/--
  Concreteness predicate (existence predicate, E!).

  `Concrete w x` holds when x is spatiotemporally located at world w.
  Concreteness is world-relative: an object may be concrete at some
  worlds and not others.
-/
axiom Concrete : World → World → Prop

-- §2  Defined notions
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

-- §3  Axioms
/--
  Ordinary objects cannot encode properties (axiom β).

  If x is ordinary then necessarily x encodes no property.
  This is the fundamental separation between the two modes of
  predication: only abstract objects have an encoding extension.
-/
axiom ordinary_no_encoding :
  ∀ x : World, O! x → □ (fun w => ¬ ∃ F : Property, Enc w F) x

/--
  Comprehension principle for abstract objects.

  For every condition φ on properties there exists an abstract object
  that encodes a property F if and only if φ F.  This is the generating
  principle for the abstract-object hierarchy: numbers, sets, possible
  worlds, Platonic forms, etc. are all instances.
-/
axiom Comprehension :
  ∀ φ : Property → Prop,
    ∃ x : World,
      A! x ∧ ∀ F : Property, Enc x F ↔ φ F

-- §4  Theorems
/--
  Abstract and ordinary objects are disjoint (A! and O! partition objects).

  No object can be both possibly concrete and not possibly concrete.
-/
theorem abstract_not_ordinary :
    ∀ x : World, ¬ (A! x ∧ O! x) :=
  fun _ ⟨ha, ho⟩ => ha ho

/--
  Canonical instance from comprehension: the abstract object whose
  encoding extension is exactly {G | φ G} encodes G iff φ G.

  This is the immediately useful corollary of Comprehension: one can
  always extract the particular abstract object and appeal to the
  biconditional for any specific property G.
-/
theorem comprehension_encoding_spec :
    ∀ (φ : Property → Prop) (G : Property),
      ∃ x : World, A! x ∧ (Enc x G ↔ φ G) := by
  intro φ G
  obtain ⟨x, hA, hspec⟩ := Comprehension φ
  exact ⟨x, hA, hspec G⟩

/--
  Abstract objects can encode properties.

  Comprehension guarantees that for any non-empty φ there is an
  abstract object with a non-empty encoding extension.  More directly,
  any φ that holds of some property F witnesses an abstract object
  encoding F.
-/
theorem abstract_objects_encode :
    ∀ (F : Property),
      ∃ x : World, A! x ∧ Enc x F := by
  intro F
  obtain ⟨x, hA, hspec⟩ := Comprehension (fun G => G = F)
  exact ⟨x, hA, (hspec F).mpr rfl⟩

-- §5  Identity of abstract objects
/--
  Encoding-identity of abstract objects (Zalta's identityₐ).

  Two abstract objects are identityₐ-related iff they are both abstract
  and encode exactly the same properties.  For abstract objects, unlike
  ordinary ones, identity is fixed by the encoding extension rather than
  by the exemplification of properties — this is the defining move of
  abstract object theory.
-/
def IdentityA (x y : World) : Prop :=
  A! x ∧ A! y ∧ ∀ F : Property, Enc x F ↔ Enc y F

notation:50 x " =ₐ " y => IdentityA x y

/--
  Identityₐ is reflexive on abstract objects.
-/
theorem identityA_refl (x : World) (hx : A! x) : x =ₐ x :=
  ⟨hx, hx, fun _ => Iff.rfl⟩

/--
  Identityₐ is symmetric.
-/
theorem identityA_symm (x y : World) (h : x =ₐ y) : y =ₐ x :=
  ⟨h.2.1, h.1, fun F => (h.2.2 F).symm⟩

/--
  Identityₐ is transitive.
-/
theorem identityA_trans (x y z : World)
    (hxy : x =ₐ y) (hyz : y =ₐ z) : x =ₐ z :=
  ⟨hxy.1, hyz.2.1, fun F => (hxy.2.2 F).trans (hyz.2.2 F)⟩

/--
  Extensionality for abstract objects.

  Abstract objects that encode exactly the same properties are identical.
  Like `situation_extensionality`, this cannot be derived from the
  intensional primitives — Enc is a bare relation with nothing forcing
  coextensive encoders to coincide — and must be postulated.  It is the
  encoding-level analogue of the extensionality of situations.
-/
axiom abstract_extensionality :
  ∀ x y : World,
    A! x → A! y → (∀ F : Property, Enc x F ↔ Enc y F) → x = y

/--
  Identityₐ collapses to genuine identity.

  Under `abstract_extensionality`, the defined encoding-identity relation
  is not merely an equivalence but coincides with `=` on abstract objects.
-/
theorem identityA_implies_eq (x y : World) (h : x =ₐ y) : x = y :=
  abstract_extensionality x y h.1 h.2.1 h.2.2

/--
  Comprehension yields a *unique* abstract object.

  For every condition φ on properties there is exactly one abstract
  object encoding precisely the properties satisfying φ.  Existence is
  `Comprehension`; uniqueness is `abstract_extensionality`, which forces
  any two such objects to have the same encoding extension and hence to
  be identical.  This upgrades comprehension from a mere existence
  principle to a genuine definite description of abstract objects.
-/
theorem abstract_object_unique :
    ∀ φ : Property → Prop,
      ∃ x : World,
        (A! x ∧ ∀ F : Property, Enc x F ↔ φ F) ∧
        ∀ y : World, (A! y ∧ ∀ F : Property, Enc y F ↔ φ F) → y = x := by
  intro φ
  obtain ⟨x, hAx, hx⟩ := Comprehension φ
  refine ⟨x, ⟨hAx, hx⟩, ?_⟩
  rintro y ⟨hAy, hy⟩
  exact abstract_extensionality y x hAy hAx
    (fun F => (hy F).trans (hx F).symm)
