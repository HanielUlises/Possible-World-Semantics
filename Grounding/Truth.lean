import Grounding.Objects
import Grounding.Propositions

/-
  TRUTH IN SITUATIONS

  Truth-in is constrained by axioms connecting it to
  propositional encoding via properties, following the
  Prover9 axiomatization used in the metatheoretic proofs.
-/

/--
  Truth of a proposition in a situation (or world).
-/
axiom TrueIn : World → Propn → Prop

notation:30 x " ⊨ " p => TrueIn x p

/--
  Propositional encoding via properties.

  A proposition p is encoded in an object x iff there exists
  a property F such that F = VAC p and x encodes F.
-/
axiom Encp_def :
  ∀ x : World, ∀ p : Propn,
    Object x →
      (Encp x p ↔
        ∃ F : Property, F = VAC p ∧ Enc x F)

/--
  Truth reduces to propositional encoding.
-/
axiom TrueIn_def :
  ∀ x : World, ∀ p : Propn,
    Object x →
      ((x ⊨ p) ↔ Encp x p)

/-
  OBTAINING AT AN INDEX

  Situated truth `s ⊨ p` is partial: a situation may leave a
  proposition undecided.  The classical truth clauses therefore do
  not belong to `⊨`.  They govern a separate relation, `Obtains v p`,
  read "p is the case at index v", where indices are the points over
  which □ and ◊ quantify.  Worlds are then characterised as the
  situations whose truths could coincide with what obtains
  (`Worldhood`), and the classical behaviour of `⊨` at worlds is
  derived rather than postulated (Situation/Worlds.lean).

  Stating the classical clauses for `⊨` at every situation forces
  every situation to decide every proposition, and together with the
  meet axioms collapses all situations into one.
-/

/-- p is the case at index v (truth simpliciter, relative to v). -/
axiom Obtains : World → Propn → Prop

/-- Negation is classical at an index. -/
axiom Obtains_neg :
  ∀ (v : World) (p : Propn),
    Obtains v (¬ₚ p) ↔ ¬ Obtains v p

/-- Conjunction is classical at an index. -/
axiom Obtains_conj :
  ∀ (v : World) (p q : Propn),
    Obtains v (p ∧ₚ q) ↔ Obtains v p ∧ Obtains v q

/-- Disjunction is classical at an index. -/
axiom Obtains_disj :
  ∀ (v : World) (p q : Propn),
    Obtains v (p ∨ₚ q) ↔ Obtains v p ∨ Obtains v q

/-- Implication is material at an index. -/
axiom Obtains_impl :
  ∀ (v : World) (p q : Propn),
    Obtains v (p →ₚ q) ↔ (Obtains v p → Obtains v q)

/--
  Equal vacuous properties have the same obtaining conditions.

  In Zalta's theory this follows from β-conversion: an object
  exemplifies `[λy p]` iff p, so if `[λy p] = [λy q]` then p and q are
  materially equivalent.  The development has no exemplification
  relation, so the consequence is postulated directly, at every index.
  It is weaker than injectivity of `VAC` and is compatible with
  necessarily equivalent but distinct propositions.
-/
axiom VAC_congr :
  ∀ (p q : Propn), VAC p = VAC q →
    ∀ v : World, Obtains v p ↔ Obtains v q

/-- Truth in an object is encoding of the corresponding vacuous
    property. -/
theorem TrueIn_iff_Enc (x : World) (hx : Object x) (p : Propn) :
    (x ⊨ p) ↔ Enc x (VAC p) := by
  rw [TrueIn_def x p hx, Encp_def x p hx]
  exact ⟨fun ⟨F, hF, he⟩ => hF ▸ he, fun he => ⟨VAC p, rfl, he⟩⟩
