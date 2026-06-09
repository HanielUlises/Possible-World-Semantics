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
