import Grounding.Ontology
import Grounding.Truth
import Grounding.Parthood
import Modality.Operators
import Grounding.AbstractObjects

/-
  CORE DEFINITIONS OF SITUATION SEMANTICS

  This stage introduces the standard notions used in
  possible-worlds and situation semantics.

  All notions are defined rather than postulated.
  No metaphysical or modal assumptions are made beyond
  those already encoded in the primitive relations.
-/

/--
  The actual index: the point of evaluation at which "p is the case"
  means that p is true simpliciter.
-/
axiom actualIndex : World

/--
  The actual world (Zalta 1993): the abstract object that encodes
  exactly the vacuous properties `VAC p` of the propositions p that
  obtain at the actual index.  It exists by `Comprehension`, and is
  unique by `abstract_extensionality`.  That it is a situation whose
  truths are exactly what obtains is a theorem
  (`actualWorld_faithful`, Situation/Worlds.lean).
-/
noncomputable def actualWorld : World :=
  Classical.choose (Comprehension (fun F => ∃ p : Propn, F = VAC p ∧ Obtains actualIndex p))

/--
  Persistence of a proposition.

  A proposition is persistent iff, whenever it is true
  in a situation, it remains true in all situations
  that extend it (in the parthood sense).

  This captures the idea that information carried by a
  situation cannot be lost when the situation is enlarged.
-/
def Persistent (p : Propn) : Prop :=
  ∀ s s' : World,
    Situation s →
    Situation s' →
    (s ⊨ p) →
    (s ⊴ s') →
    (s' ⊨ p)
    
/--
  Actuality of a situation.

  A situation is actual iff every proposition that is
  true in it is true simpliciter.

  Actuality is therefore not a modal notion but a
  correctness condition relating situational truth
  to truth tout court.
-/
def Actual (s : World) : Prop :=
  ∀ p : Propn, (s ⊨ p) → Obtains actualIndex p


/--
  Possibility of a situation.

  A situation is possible iff it could be actual: at some
  index, everything true in it obtains.

  This is the minimal modal notion needed to connect
  situations with possible worlds.
-/
def Possible (s : World) : Prop :=
  ◊ (fun v => ∀ p : Propn, (s ⊨ p) → Obtains v p) actualIndex

/--
  Worldhood.

  A world is a situation that could make exactly the
  true propositions true (Zalta: ◊∀p(s ⊨ p ↔ p)).
  "p is true" is relative to the index of evaluation, so
  it is rendered as `Obtains v p`.

  Maximality and consistency of worlds are derived from
  this definition (Situation/Worlds.lean).
-/
def Worldhood (s : World) : Prop :=
  Situation s ∧
  ◊ (fun v => ∀ p : Propn, (s ⊨ p) ↔ Obtains v p) actualIndex

/--
  Maximality (first sense).

  A situation is maximal₁ iff for every proposition,
  either it or its negation is true in the situation.

  This corresponds to classical completeness with
  respect to propositional content.
-/
def Maximal₁ (s : World) : Prop :=
  ∀ p : Propn, (s ⊨ p) ∨ (s ⊨ ¬ₚ p)

/--
  Partiality (first sense).

  A situation is partial₁ iff there exists at least one
  proposition that is left undetermined: neither it nor
  its negation is true.
-/
def Partial₁ (s : World) : Prop :=
  ∃ p : Propn, ¬ (s ⊨ p) ∧ ¬ (s ⊨ ¬ₚ p)

/--
  Maximality (second sense).

  A situation is maximal₂ iff every proposition is true
  in it.

  This is a stronger notion than maximal₁ and is not
  generally satisfiable without triviality.
-/
def Maximal₂ (s : World) : Prop :=
  ∀ p : Propn, s ⊨ p

/--
  Partiality (second sense).

  A situation is partial₂ iff there exists at least one
  proposition that is not true in it.
-/
def Partial₂ (s : World) : Prop :=
  ∃ p : Propn, ¬ (s ⊨ p)

/--
  Consistency.

  A situation is consistent iff it does not make both
  a proposition and its negation true.

  This is the minimal non-contradiction condition
  imposed on situational truth.
-/
def Consistent (s : World) : Prop :=
  ¬ ∃ p : Propn, (s ⊨ p) ∧ (s ⊨ ¬ₚ p)
