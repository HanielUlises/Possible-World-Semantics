-- Test/Consistency.lean
import Grounding.Ontology
import Grounding.Parthood
import Situation.Theorems

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
