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
theorem depends_refl (s : World) : s ≺ s :=
  fun _ _ hsu => hsu

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

/-- A whole depends on each of its parts.
    If s' is a part of s, then every situation that includes s also
    includes s', by transitivity of parthood.  This is the derivable
    direction linking ⊴ and ≺; the converse (a part depends on its
    wholes) is not derivable, and postulating it collapses parthood
    to identity on situations (see README.md § OP-2b). -/
theorem whole_depends_on_part (s s' : World) (hpart : s' ⊴ s) : s ≺ s' :=
  fun u _ hsu => partOf_trans s' s u hpart hsu

/-- Dependence is inherited from parts.
    If s' is a part of s and s' depends on s'', then s depends on s''.
    A whole requires whatever its parts require.

    Resolves OP-2b.  The original statement (s ⊴ s' and s' ≺ s'' give
    s ≺ s'') needed s ⊴ s' → s ≺ s', which is not derivable: ≺ points
    from a situation to its parts, not to its wholes.  Postulating it
    forces s' ⊴ s (take u := s), so by parthood_antisymm every pair of
    situations related by ⊴ is identical.  The statement is therefore
    oriented along whole_depends_on_part, and closes without axioms. -/
theorem parthood_implies_depends (s s' s'' : World)
    (hpart : s' ⊴ s)
    (hdep  : s' ≺ s'') : s ≺ s'' :=
  depends_trans s s' s'' (whole_depends_on_part s s' hpart) hdep

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

/-- Strict (proper) dependence: s depends on a distinct s'.
    This excludes the trivial self-dependence of depends_refl, isolating
    the cases where one situation genuinely requires another. -/
def StrictlyDepends (s s' : World) : Prop :=
  (s ≺ s') ∧ s ≠ s'

/-- Grounding as asymmetric dependence.
    s' grounds s when s depends on s' but not conversely.  This is the
    Fine–Correia reading of grounding as a strict, direction-fixed
    relation: the ground is that on which the grounded asymmetrically
    depends. -/
def WeaklyGrounds (s s' : World) : Prop :=
  (s' ≺ s) ∧ ¬ (s ≺ s')

/-- Grounding is asymmetric by construction.
    Nothing both grounds and is grounded by the same situation, since
    the second conjunct of WeaklyGrounds explicitly denies the converse
    dependence. -/
theorem weakly_grounds_asymm (s s' : World)
    (h : WeaklyGrounds s s') : ¬ WeaklyGrounds s' s :=
  fun h' => h.2 h'.1

/-- Mutual dependence is symmetric.
    Co-dependence is a symmetric relation: if each of two situations
    requires the other, the relation is unchanged by swapping them. -/
theorem mutual_depends_symm (s s' : World)
    (h : MutuallyDependent s s') : MutuallyDependent s' s :=
  ⟨h.2, h.1⟩

/-- Mutual parthood induces mutual dependence.
    If two situations are parts of each other, then each depends on the
    other, so they are ontologically co-dependent.  (By parthood
    antisymmetry such situations are in fact identical; the point here
    is that parthood in both directions already suffices for the
    dependence structure via whole_depends_on_part.) -/
theorem mutual_dependence_from_parthood (s s' : World)
    (hss' : s ⊴ s') (hs's : s' ⊴ s) : MutuallyDependent s s' :=
  ⟨whole_depends_on_part s s' hs's,
   whole_depends_on_part s' s hss'⟩

/-- Foundational and derivative situations exhaust the space.
    A situation fails to be foundational exactly when it is derivative:
    the failure of "every dependence is already contained" is the
    existence of an uncontained dependence.  The two notions are strict
    negations of each other. -/
theorem not_foundational_iff_derivative (s : World) :
    ¬ Foundational s ↔ Derivative s := by
  constructor
  · intro h
    rcases Classical.em (Derivative s) with hd | hnd
    · exact hd
    · exfalso
      apply h
      intro s' hdep
      rcases Classical.em (s ⊴ s') with hp | hnp
      · exact hp
      · exact absurd ⟨s', hdep, hnp⟩ hnd
  · rintro ⟨s', hdep, hnpart⟩ hfound
    exact hnpart (hfound s' hdep)
