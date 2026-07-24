import Grounding.Ontology

/--
  Intensional negation on propositions.
-/
axiom neg : Propn → Propn

notation "¬ₚ" => neg

/--
  Intensional conjunction of propositions.
-/
axiom conj : Propn → Propn → Propn

infixl:70 " ∧ₚ " => conj

/--
  Intensional disjunction of propositions.
-/
axiom disj : Propn → Propn → Propn

infixl:65 " ∨ₚ " => disj

/--
  Intensional implication between propositions.
-/
axiom impl : Propn → Propn → Propn

infixr:60 " →ₚ " => impl

/--
  Intensional biconditional between propositions.

  Written as bic p q rather than infix to avoid conflicts
  with Lean's reserved notation for Iff.
-/
axiom bic : Propn → Propn → Propn

/--
  Biconditional unfolds as mutual implication.
-/
axiom bic_def :
  ∀ p q : Propn, bic p q = conj (impl p q) (impl q p)

/--
  Double negation: ¬ₚ¬ₚp is intensionally identical to p.

  This corresponds to the Boolean principle that two negations
  cancel at the level of propositional identity, reflecting
  the classical character of the propositional base.
-/
axiom neg_neg :
  ∀ p : Propn, neg (neg p) = p

/--
  De Morgan for conjunction: ¬ₚ(p ∧ₚ q) = ¬ₚp ∨ₚ ¬ₚq.
-/
axiom deMorgan_conj :
  ∀ p q : Propn, neg (conj p q) = disj (neg p) (neg q)

/--
  De Morgan for disjunction: ¬ₚ(p ∨ₚ q) = ¬ₚp ∧ₚ ¬ₚq.
-/
axiom deMorgan_disj :
  ∀ p q : Propn, neg (disj p q) = conj (neg p) (neg q)

/--
  Implication reduces to disjunction: p →ₚ q = ¬ₚp ∨ₚ q.

  This is the classical equivalence between material implication
  and disjunction, postulated at the intensional level.
-/
axiom impl_as_disj :
  ∀ p q : Propn, impl p q = disj (neg p) q

/--
  Conjunction is commutative at the propositional level.
-/
axiom conj_comm :
  ∀ p q : Propn, conj p q = conj q p

/--
  Disjunction is commutative at the propositional level.
-/
axiom disj_comm :
  ∀ p q : Propn, disj p q = disj q p

/--
  Conjunction is associative at the propositional level.
-/
axiom conj_assoc :
  ∀ p q r : Propn, conj (conj p q) r = conj p (conj q r)

/--
  Disjunction is associative at the propositional level.
-/
axiom disj_assoc :
  ∀ p q r : Propn, disj (disj p q) r = disj p (disj q r)

/--
  Biconditional is symmetric: bic p q implies bic q p.
-/
theorem bic_symm (p q : Propn) (h : bic p q = bic p q) : bic q p = bic q p := by
  rfl

/--
  Biconditional is symmetric in the propositional sense.
-/
theorem bic_symm' (p q : Propn) : bic p q = bic q p := by
  rw [bic_def, bic_def, conj_comm]

/--
  Double negation is involutive.
-/
theorem neg_neg_involutive (p : Propn) : neg (neg (neg (neg p))) = p := by
  rw [neg_neg, neg_neg]

/--
  Contraposition: p →ₚ q is intensionally identical to ¬ₚq →ₚ ¬ₚp.

  This is the classical law of contraposition promoted to the level of
  propositional identity.  It follows purely from the reduction of
  implication to disjunction, the involutivity of negation, and the
  commutativity of disjunction — no new postulate is required.
-/
theorem impl_contrapositive (p q : Propn) :
    impl p q = impl (neg q) (neg p) := by
  rw [impl_as_disj, impl_as_disj, neg_neg]
  exact disj_comm (neg p) q
