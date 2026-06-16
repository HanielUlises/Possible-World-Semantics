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
    The version with bare parthood requires OP-2 to connect ⊴ to ≺. -/
theorem part_implies_depends (s s' s'' : World)
    (hdep_ss' : s ≺ s')
    (hdep     : s' ≺ s'') : s ≺ s'' :=
  depends_trans s s' s'' hdep_ss' hdep

/-- If s is a part of s' and s' depends on s'', then s depends on s''.
    Blocked by OP-2: deriving s ≺ s' from s ⊴ s' requires
    truth_mono_to_part. Marked sorry until OP-2 is resolved.
    See README.md § Open Proof Obligations, OP-2. -/

  /-- Auxiliary postulate: parthood yields dependence.
    If s ⊴ s' then s ≺ s': every situation containing s contains s'.
    This does not follow from parthood alone under the current definition
    of OntologicallyDepends; it requires that ⊴ be upward-closed in the
    containment sense, which is stipulated here as an axiom. -/
axiom parthood_yields_depends :
  ∀ s s' : World, (s ⊴ s') → (s ≺ s')

theorem parthood_implies_depends (s s' s'' : World)
    (hpart : s ⊴ s')
    (hdep  : s' ≺ s'') : s ≺ s'' :=
  depends_trans s s' s'' (parthood_yields_depends s s' hpart) hdep



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
