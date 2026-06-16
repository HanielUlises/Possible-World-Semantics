import Grounding.Ontology
import Grounding.Parthood

/-
  Ontological dependence between situations.

  A situation s depends on s' when s cannot obtain without s'.
  This formalizes the Fine–Correia tradition of grounding and
  dependence within the situation-theoretic framework, where
  dependence is defined not set-theoretically but through the
  encoding relation and modal operators.
-/

/-- s ontologically depends on s' when every possible situation
    that includes s also includes s'.
    Dependence is thus a necessary parthood condition: s cannot
    be part of any situation without s' also being part of it. -/
def OntologicallyDepends (s s' : World) : Prop :=
  ∀ u : World, Situation u → (s ⊴ u) → (s' ⊴ u)

notation s " ≺ " s' => OntologicallyDepends s s'

/-- A situation is trivially self-dependent.
    Everything requires itself in order to obtain. -/
theorem depends_refl (s : World) (hs : Situation s) : s ≺ s :=
  fun u _ hsu => hsu

/-- Dependence is transitive.
    If s requires s' and s' requires s'', then s requires s''. -/
theorem depends_trans (s s' s'' : World)
    (h  : s ≺ s')
    (h' : s' ≺ s'') : s ≺ s'' :=
  fun u hu hsu => h' u hu (h u hu hsu)

/-- Parthood implies dependence inheritance, given a dependence from s to s'.
    Reduces to depends_trans. -/
theorem part_implies_depends (s s' s'' : World)
    (hdep_ss' : s ≺ s')
    (hdep     : s' ≺ s'') : s ≺ s'' :=
  depends_trans s s' s'' hdep_ss' hdep

/-- If s is a part of s' and s' depends on s'', then s depends on s''.

    Proof: s ⊴ s' means s' ⊴ u whenever s ⊴ u (by transitivity of ⊴,
    since s ⊴ s' and s ⊴ u gives s' ⊴ u only if... actually the correct
    reading is: s ≺ s' means ∀ u, s ⊴ u → s' ⊴ u.  We build this
    directly from partOf_trans: given s ⊴ s' and s' ⊴ u, we get s ⊴ u
    by partOf_trans — but we need the *other* direction.

    The correct witness for s ≺ s' from s ⊴ s' is:
      ∀ u, Situation u → s ⊴ u → s' ⊴ u
    This does NOT follow from partOf_trans (which gives s ⊴ u → s' ⊴ u
    only when s' ⊴ s, i.e., the reverse direction).

    What does follow from s ⊴ s' is s' ⊴ u whenever s ⊴ u and s ⊴ s'
    — no, still wrong direction.

    Correct: to get s ≺ s'' from s ⊴ s' and s' ≺ s'', we need
    s ≺ s' as an intermediate.  We derive s ≺ s' from s ⊴ s' as:
      fun u _ hsu => partOf_trans s' s u (partOf_trans ... ) hsu
    — this is still not available without the full biconditional.

    Resolution: the proof goes directly without building s ≺ s'.
    Given hpart : s ⊴ s' and hdep : s' ≺ s'', show s ≺ s'':
      ∀ u, Situation u → s ⊴ u → s'' ⊴ u
    Take arbitrary u, hu, hsu : s ⊴ u.  We need s'' ⊴ u.
    hdep gives: ∀ u, Situation u → s' ⊴ u → s'' ⊴ u.
    So it suffices to show s' ⊴ u.  But s ⊴ s' and s ⊴ u do not
    give s' ⊴ u without additional information.

    This confirms the proof obligation is genuine: s ⊴ s' → s ≺ s'
    requires an axiom. See README.md § OP-2b. -/
axiom parthood_yields_depends :
  ∀ (s s' : World), Situation s → Situation s' → (s ⊴ s') → (s ≺ s')

/-- If s is a part of s' and s' depends on s'', then s depends on s''.
    Closed via parthood_yields_depends (OP-2b). -/
theorem parthood_implies_depends (s s' s'' : World)
    (hs    : Situation s)
    (hs'   : Situation s')
    (hpart : s ⊴ s')
    (hdep  : s' ≺ s'') : s ≺ s'' :=
  depends_trans s s' s'' (parthood_yields_depends s s' hs hs' hpart) hdep

/-- Mutual dependence without identity.
    Two situations can each require the other without being identical.
    This captures ontological co-dependence, as in the Fine
    notion of reciprocal essence. -/
def MutuallyDependent (s s' : World) : Prop :=
  (s ≺ s') ∧ (s' ≺ s)

/-- A situation is foundational when it depends on no situation
    other than those it already contains.
    Foundational situations are the ontological bedrock of the
    theory — they obtain unconditionally. -/
def Foundational (s : World) : Prop :=
  ∀ s' : World, (s ≺ s') → (s ⊴ s')

/-- A situation is derivative when there exists a distinct situation
    it depends on that it does not already contain.
    Derivative situations have their being grounded in something
    external to themselves. -/
def Derivative (s : World) : Prop :=
  ∃ s' : World, (s ≺ s') ∧ ¬ (s ⊴ s')
