import Modality.Frames

/-
  Modal operators and S5 theorems.

  This development introduces a minimal modal vocabulary
  together with theorems characterizing S5 modal logic.

  Box is defined by explicit quantification over R-accessible
  worlds rather than left as a free primitive. This grounds the
  modal operators mechanistically in the Kripke frame: □ p w
  unfolds to ∀ v, R w v → p v, and every S5 principle becomes
  a calculation over R rather than an ungrounded assertion.

  Diamond retains the original negation-dual definition exactly,
  preserving intensional character and leaving all downstream
  code that unfolds ◊ unchanged.

  Every axiom from the original file is replaced by a theorem.
  The four derived theorems are preserved verbatim and continue
  to compile because K, T, Four, Five, Nec, PossNec still exist
  as names — they are just theorems now rather than axioms.
-/

/--
  Necessity operator.

  □ p w holds iff p holds at every R-accessible world.
  Defined rather than postulated: the mechanism is explicit
  quantification over the accessibility relation from Frames.lean.
-/
def Box (p : World → Prop) (w : World) : Prop :=
  ∀ v : World, R w v → p v

/--
  Possibility operator.

  ◊ p is defined as the dual of necessity.
  Definition preserved verbatim from the original file.
-/
def Diamond (p : World → Prop) : World → Prop :=
  fun w => ¬ Box (fun v => ¬ p v) w

notation "□" => Box
notation "◊" => Diamond

/-
  S5 theorems.

  These were axioms in the original file. Each is now a theorem
  whose proof makes the frame-level mechanism explicit.
  Names, types, and docstrings are preserved exactly.
-/

/--
  Axiom K (distribution).

  Necessity distributes over implication.
-/
theorem K :
    ∀ (p q : World → Prop) (w : World),
      □ (fun v => p v → q v) w →
      □ p w →
      □ q w :=
  fun _ _ _ hpq hp v hrwv => hpq v hrwv (hp v hrwv)

/--
  Axiom T (reflexivity).

  What is necessary is the case.
  Proof: R_refl gives R w w, so the universal in □ p w applies at w itself.
-/
theorem T :
    ∀ (p : World → Prop) (w : World),
      □ p w → p w :=
  fun _ w h => h w (R_refl w)

/--
  Axiom 4 (positive introspection).

  What is necessary is necessarily necessary.
  Proof: to show □ p at any v accessible from w, and then □ p at any u
  accessible from v, use R_trans to get R w u directly and apply h.
-/
theorem Four :
    ∀ (p : World → Prop) (w : World),
      □ p w → □ (□ p) w :=
  fun _ w h v hrwv u hruv => h u (R_trans w v u hrwv hruv)

/--
  Axiom 5 (negative introspection).

  What is possible is necessarily possible.
  Proof: ◊ p w means ¬ □ (¬p) w. At any v accessible from w, we must
  show ¬ □ (¬p) v. If □ (¬p) v held, it would cover every world u
  accessible from v; but by R_symm and R_trans every world accessible
  from w is accessible from v, contradicting ◊ p w.
-/
theorem Five :
    ∀ (p : World → Prop) (w : World),
      ◊ p w → □ (◊ p) w := by
  intro p w h v hrwv hbox
  apply h
  intro u hrwu
  exact hbox u (R_trans v w u (R_symm w v hrwv) hrwu)

/-
  OP-1a resolved: Necessitation.
  OP-1b resolved: Possible-necessity collapse.
-/

/-- Necessitation encodes the closure of the logic under universal truth:
    any proposition holding at every world is necessary at every world.
    Without this rule no theorem of the form □φ w is derivable from
    universal facts alone, leaving S5 incomplete as a deductive system.

    Resolves OP-1a — now a theorem rather than an axiom.
    Proof: the universal hypothesis h gives p at any world v directly;
    the accessibility hypothesis is not needed and is discarded. -/
theorem Nec : ∀ (p : World → Prop), (∀ w, p w) → ∀ w, □ p w :=
  fun _ h _ v _ => h v

/-- Bridge between possible necessity and necessity.
    In S5 this holds at the frame level via symmetry and transitivity
    of the accessibility relation.

    Resolves OP-1b — now a theorem rather than an axiom.

    Proof mechanism: ◊ (□ p) w unfolds via the negation-dual to
    ¬ (∀ u, R w u → ¬ □ p u). The goal is □ p w = ∀ v, R w v → p v,
    which it suffices to strengthen to ∀ x, p x. We assume ¬ (∀ x, p x)
    for contradiction: push_neg yields ∃ x, ¬ p x. We then discharge h
    by exhibiting ∀ u, R w u → ¬ □ p u — given any u and □ p u, applying
    it at the witness x via R_refl gives p x, contradicting ¬ p x. -/
theorem PossNec :
    ∀ (p : World → Prop) (w : World),
      ◊ (fun w' => □ p w') w → □ p w :=
  fun p w h v _ =>
    Classical.byContradiction (fun hnpv =>
      h (fun u _ hBoxpu =>
        hnpv (hBoxpu v (R_refl v))))

/-- Necessity is monotone with respect to implication.
    If a conditional holds necessarily and its antecedent holds necessarily,
    the consequent holds necessarily. This is the semantic content of Axiom K
    stated as a derived rule rather than a bare axiom schema. -/
theorem Box_monotone (p q : World → Prop) (w : World)
    (hpq : ∀ v, p v → q v) (hp : □ p w) : □ q w :=
  K p q w (Nec (fun v => p v → q v) hpq w) hp

/-- The characteristic thesis of S5: whatever is possibly necessary is necessary.
    This collapses the distinction between the necessity of a proposition and
    the necessity of its possibility, giving the modal logic its strongest
    classical form. -/
theorem S5_characteristic (p : World → Prop) (w : World)
    (h : ◊ (fun w' => □ p w') w) : □ p w :=
  PossNec p w h

/-- Iterated necessity: a necessary truth is necessarily necessary.
    This corresponds to the positive introspection of necessity,
    ensuring that the accessibility relation is transitive at the frame level. -/
theorem Box_Box_of_Box (p : World → Prop) (w : World)
    (h : □ p w) : □ (□ p) w :=
  Four p w h

/-- Universal truth entails possibility.
    A proposition true at every world cannot be excluded by any world,
    so it is witnessed as possible at the actual world. -/
theorem Nec_implies_Pos (p : World → Prop) (w : World)
    (h : ∀ v, p v) : ◊ p w := by
  intro hbox
  exact T (fun v => ¬ p v) w hbox (h w)

/-
  DUALITY, DISTRIBUTION, AND CONTINGENCY

  This section develops the classical modal calculus on top of the
  S5 core above.  Every result is a calculation over R (which is the
  universal relation, from Frames.lean) and adds no new postulate.
  The theorems make the □/◊ interplay explicit and introduce the
  standard contingency vocabulary as defined notions.
-/

/-- What is necessary is possible (the modal square of opposition).
    In any reflexive frame necessity entails possibility: if p holds at
    every accessible world it holds at some accessible world, since the
    evaluation world itself is accessible by R_refl.  This is the T-dual
    of the T axiom. -/
theorem Diamond_of_Box (p : World → Prop) (w : World)
    (h : □ p w) : ◊ p w :=
  fun hbox => hbox w (R_refl w) (h w (R_refl w))

/-- Necessity is the dual of possibility.
    □ p is definitionally ¬ ◊ ¬p up to a double negation on the matrix;
    the equivalence makes the duality between the two operators explicit
    rather than leaving it implicit in the definition of ◊. -/
theorem Box_iff_not_Diamond_not (p : World → Prop) (w : World) :
    □ p w ↔ ¬ ◊ (fun v => ¬ p v) w := by
  constructor
  · intro hbox hdia
    exact hdia (fun v hrwv hnp => hnp (hbox v hrwv))
  · intro hdia v hrwv
    rcases Classical.em (p v) with hp | hnp
    · exact hp
    · exact absurd (fun hbox => hbox v hrwv hnp) hdia

/-- Possibility is monotone with respect to implication.
    If p entails q pointwise, then whatever is possibly p is possibly q:
    a world witnessing the possibility of p also witnesses that of q.
    This is the ◊-analogue of Box_monotone. -/
theorem Diamond_monotone (p q : World → Prop) (w : World)
    (hpq : ∀ v, p v → q v) (hp : ◊ p w) : ◊ q w :=
  fun hboxnq => hp (fun v hrwv hpv => hboxnq v hrwv (hpq v hpv))

/-- Possibility distributes over disjunction.
    A disjunction is possible iff one of its disjuncts is possible.
    The right-to-left direction is monotonicity; the left-to-right
    direction is the characteristic K-level validity, obtained by
    contradiction from the necessity of both negated disjuncts. -/
theorem Diamond_distrib_disj (p q : World → Prop) (w : World) :
    ◊ (fun v => p v ∨ q v) w ↔ ◊ p w ∨ ◊ q w := by
  constructor
  · intro h
    rcases Classical.em (◊ p w) with hp | hnp
    · exact Or.inl hp
    · refine Or.inr ?_
      intro hboxnq
      apply h
      intro v hrwv hpq
      cases hpq with
      | inl hpv => exact hnp (fun hbox => hbox v hrwv hpv)
      | inr hqv => exact hboxnq v hrwv hqv
  · rintro (hp | hq)
    · exact Diamond_monotone p _ w (fun _ hpv => Or.inl hpv) hp
    · exact Diamond_monotone q _ w (fun _ hqv => Or.inr hqv) hq

/-- Necessity distributes over conjunction.
    A conjunction is necessary iff both conjuncts are necessary.
    Both directions are immediate from the definition of □ as a
    universal quantifier over accessible worlds. -/
theorem Box_distrib_conj (p q : World → Prop) (w : World) :
    □ (fun v => p v ∧ q v) w ↔ □ p w ∧ □ q w := by
  constructor
  · intro h
    exact ⟨fun v hrwv => (h v hrwv).1, fun v hrwv => (h v hrwv).2⟩
  · rintro ⟨hp, hq⟩ v hrwv
    exact ⟨hp v hrwv, hq v hrwv⟩

/-- Necessity of a proposition. -/
def Necessary (p : World → Prop) (w : World) : Prop :=
  □ p w

/-- Impossibility of a proposition: its negation is necessary. -/
def Impossible (p : World → Prop) (w : World) : Prop :=
  □ (fun v => ¬ p v) w

/-- Contingency of a proposition: it is possibly true and possibly false.
    Contingent propositions are those the modal structure leaves open in
    both directions — neither necessary nor impossible. -/
def Contingent (p : World → Prop) (w : World) : Prop :=
  ◊ p w ∧ ◊ (fun v => ¬ p v) w

/-- The necessary is not impossible.
    Since necessity entails possibility (Diamond_of_Box), a necessary
    proposition is possibly true, hence not necessarily false. -/
theorem necessary_not_impossible (p : World → Prop) (w : World)
    (h : Necessary p w) : ¬ Impossible p w :=
  fun himp => (Box_iff_not_Diamond_not p w).mp h (Diamond_of_Box _ w himp)

/-- The contingent is not necessary.
    A contingent proposition is possibly false, so its necessity would
    contradict the possibility of its negation via duality. -/
theorem contingent_not_necessary (p : World → Prop) (w : World)
    (h : Contingent p w) : ¬ Necessary p w :=
  fun hnec => (Box_iff_not_Diamond_not p w).mp hnec h.2
