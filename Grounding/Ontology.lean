/-
  ontological primitives.

  this file introduces the basic entities of the theory.
  all notions are taken as primitive and governed by axioms,
  in the spirit of higher-order modal and situation semantics.
-/

/--
  the domain of objects.

  worlds and situations are not distinguished at the type level.
-/
axiom World : Type

/--
  the domain of properties.

  properties are intensional entities which may be encoded.
-/
axiom Property : Type

/--
  the domain of propositions.

  propositions are intensional and evaluated relative to situations.
-/
axiom Propn : Type

/--
  objecthood predicate.
-/
axiom Object : World → Prop

/--
  situationhood predicate.
-/
axiom Situation : World → Prop

/--
  encoding relation between objects and properties.
-/
axiom Enc : World → Property → Prop

/--
  encoding relation between objects and propositions.
-/
axiom Encp : World → Propn → Prop

/--
  vacuous abstraction operator.
-/
axiom VAC : Propn → Property

/--
  every situation is an object.

  in Zalta's abstract object theory, situations are a species
  of abstract object. Object and Situation are both primitive
  predicates here, so their inclusion cannot be derived —
  it must be postulated. This closes OP-3.
-/
axiom situation_is_object : ∀ s : World, Situation s → Object s
