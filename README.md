# Possible-World-Semantics

A Lean 4 formalization of possible-world and situation semantics, following the higher-order modal and situation-theoretic tradition of Zalta, Fine, and Barwise–Perry.

Everything is built from scratch — no Mathlib, no set theory, just primitives and axioms. Metatheoretic results proven externally in Prover9 are recorded as axioms with documentation of the proof obligation.

## Theoretical Background

The development follows the Zalta–Fine tradition. Worlds and situations are not distinguished at the type level: `World` is the single domain, and `Situation` and `Object` are predicates over it.

The central primitive is encoding (`Enc`). A situation encodes the properties that constitute its informational content. Parthood is defined encoding-first: `s ⊴ s'` holds iff every property encoded by `s` is also encoded by `s'`, matching the mereology of Barwise–Perry and the abstract object theory of Zalta.

Modal operators are axiomatic, and not reduced to Kripke frames. The S5 schemas are postulated directly:

```
□(φ → ψ) → □φ → □ψ          (K)
□φ → φ                      (T)
□φ → □□φ                    (4)
◊φ → □◊φ                    (5)
```

`Modality/Frames.lean` provides the frame-level conditions as a potential semantic grounding, but they are not wired to `Box` by default. The modal layer stays neutral with respect to frame semantics.

Extensionality is a postulate. Situations are individuated by propositional content:

```
Situation(s) ∧ Situation(s') ∧ (∀p, s ⊨ p ↔ s' ⊨ p) → s = s'
```

This cannot be derived from purely intensional primitives and must be stipulated, which is the standard move in both situation semantics and abstract object theory.

## Axiom Inventory

| Axiom | File | Status |
|---|---|---|
| `World`, `Property`, `Propn` | `Grounding/Ontology` | primitive type |
| `Object`, `Situation` | `Grounding/Ontology` | primitive predicate |
| `Enc`, `Encp`, `VAC` | `Grounding/Ontology` | primitive relation / operator |
| `situation_is_object` | `Grounding/Ontology` | predicate inclusion postulate |
| `neg` (¬ₚ) | `Grounding/Propositions` | primitive connective |
| `TrueIn` (⊨) | `Grounding/Truth` | primitive relation |
| `Encp_def` | `Grounding/Truth` | Prover9-verified metatheorem |
| `TrueIn_def` | `Grounding/Truth` | Prover9-verified metatheorem |
| `R`, `R_refl`, `R_trans`, `R_symm` | `Modality/Frames` | S5 frame conditions |
| `Box` (□) | `Modality/Operators` | primitive modal operator |
| `K`, `T`, `Four`, `Five` | `Modality/Operators` | S5 axioms |
| `Nec` | `Modality/Operators` | necessitation rule |
| `PossNec` | `Modality/Operators` | ◊□φ → □φ, S5 collapse |
| `actualWorld` | `Situation/Definitions` | designated constant |
| `situation_extensionality` | `Situation/Extensionality` | constitutive postulate |
| `situation_extensionality_via_truth` | `Situation/Theorems` | Prover9 Theorem 2 |
| `actual_implies_possible` | `Situation/Theorems` | modal postulate |
| `situation_closed_under_parthood` | `Situation/Theorems` | Prover9 Theorem 3 |
| `meet`, `meet_situation`, `TrueIn_meet` | `Situation/Infimum` | meet existence and truth conditions |

## Open Proof Obligations

Every `sorry` in the codebase corresponds to exactly one entry in this table.

| ID | Obligation | Blocks | File |
|---|---|---|---|
| OP-2b | `parthood_implies_depends` | derivation that `s ⊴ s' → s ≺ s'` | `Grounding/Dependence.lean` |
| OP-4 | `meet_le_left`, `meet_le_right`, `meet_greatest` | full lattice structure of meet | `Situation/Infimum.lean` |
| OP-5 | `no_strict_subworld` | strict subworld exclusion | `Situation/Worlds.lean` |

### OP-2b — Parthood implies dependence

`parthood_implies_depends` states that if `s ⊴ s'` and `s'` depends on `s''`, then `s` depends on `s''`. The proof requires converting `s ⊴ s'` into `s ≺ s'` (ontological dependence). `truth_mono_to_part` (resolved as OP-2) is now available, but the conversion is not immediate: `OntologicallyDepends s s'` is `∀ u, Situation u → s ⊴ u → s' ⊴ u`, which is a claim about all containing situations, not just a truth-transfer statement. Whether this follows from `s ⊴ s'` alone or requires an additional postulate remains to be determined.

### OP-4 — Lattice structure of meet

`meet_le_left`, `meet_le_right`, and `meet_greatest` all need to connect `TrueIn_meet` (which governs truth at the meet) to `PartOf` (which is defined over `Enc`). `truth_mono_to_part` is now available (OP-2 resolved), so all three should be closeable by applying it to the truth conditions given by `TrueIn_meet`. No new axioms are expected to be needed.

### OP-5 — No strict subworld

`no_strict_subworld` states that no proper part of a world is itself a world. The two `sorry` markers correspond to steps that propagate truth across the parthood relation. Both are now unblocked by the resolution of OP-2 and should be closeable using `part_truth_mono` and `truth_mono_to_part`.

## Resolved Proof Obligations

### OP-2 — Parthood via truth-monotonicity

`PartOf` is defined over `Enc` while `TrueIn` is an independent primitive. The direction

```
(∀p, s ⊨ p → s' ⊨ p) → s ⊴ s'
```

was not initially derivable, leaving the biconditional `s ⊴ s' ↔ ∀p, s ⊨ p → s' ⊨ p` half-proved and blocking antisymmetry (Theorem 5) and same-parts identity (Theorem 6) of Zalta (1993).

Closed by `truth_mono_to_part` in `Grounding/Parthood.lean`. The proof goes via `Enc_VAC_complete`, where every property encoded by a situation is of the form `VAC p`, so truth-monotonicity in the `TrueIn` sense transfers back to encoding-monotonicity in the `Enc` sense, yielding `s ⊴ s'` directly. No new axioms were needed beyond `Enc_VAC_complete` and `situation_is_object` (OP-3). With this in place, `parthood_iff_truth_inclusion`, `parthood_antisymm`, `same_parts_identity`, and `all_propositions_persistent` all close without. Metatheoretic justification check Prover9 proof `theorem4.in` at peoppenheimer.org/cm/worlds/, Theorem 4 of Zalta (1993).

### OP-1 — Necessitation and possible-necessity collapse

The necessitation rule `(∀w, φw) → ∀w, □φw` and the S5 collapse `◊□φ → □φ` are not derivable from K, T, 4, and 5 alone. Necessitation is admissible in every normal modal logic but is not a substitution instance of any of the schemas. The collapse holds in all S5 frames by euclideanity but requires a frame-level reduction or a direct postulate in a purely axiomatic development.

Both were closed by postulating `Nec` and `PossNec` in `Modality/Operators.lean`. Deriving them from `Modality/Frames.lean` remains possible but is not imposed.

### OP-3 — Situations are objects

`TrueIn_def` and `Encp_def` both require an `Object x` hypothesis. `Situation` and `Object` are independent predicates with nothing forcing their extensions to overlap. The bridge `Situation(s) → Object(s)` was postulated as `situation_is_object` in `Grounding/Ontology.lean`.

With this in place, `part_truth_mono` closes without `sorry`: the direction `s ⊴ s' → (s ⊨ p → s' ⊨ p)` is fully derived by unfolding `TrueIn_def` and `Encp_def` on both sides and applying encoding-monotonicity of `PartOf` directly.

## References

Zalta, E. *Intensional Logic and the Metaphysics of Intentionality*. MIT Press, 1988.

Fine, K. "Ontological Dependence." *Proceedings of the Aristotelian Society*, 1995.

Barwise, J. and Perry, J. *Situations and Attitudes*. MIT Press, 1983.

Oppenheimer, P. and Zalta, E. "The Computational Theory of Possible Worlds." peoppenheimer.org/cm/worlds/