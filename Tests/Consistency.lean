-- Test/Consistency.lean
import Grounding.Ontology
import Grounding.Parthood
import Situation.Theorems
import Situation.Worlds

-- Verify that parthood_antisymm has the expected signature
example : ∀ (s s' : World),
    Situation s → Situation s' →
    (s ⊴ s') → (s' ⊴ s) → s = s' :=
  parthood_antisymm

-- Verify that situation_extensionality_via_truth has the expected signature
example : ∀ s₁ s₂ : World,
    Situation s₁ → Situation s₂ →
    (∀ p : Propn, (s₁ ⊨ p) ↔ (s₂ ⊨ p)) → s₁ = s₂ :=
  situation_extensionality_via_truth

-- The actual world is faithful to the actual index.  This is derived
-- from its definition by comprehension: the only axioms beyond the
-- primitives are `Comprehension`, `VAC_congr`, `TrueIn_def` and
-- `Encp_def`.
example : Situation actualWorld ∧
    ∀ p : Propn, (actualWorld ⊨ p) ↔ Obtains actualIndex p :=
  actualWorld_faithful

#print axioms actualWorld_faithful
