-- Tests/Variants.lean
import Situation.Variants

-- If truth is classical at every object, situations collapse: any two
-- are identical.
example (hneg : ∀ (s : World) (p : Propn), (s ⊨ ¬ₚ p) ↔ ¬ (s ⊨ p))
    (s s' : World) (hs : Situation s) (hs' : Situation s') : s = s' :=
  classical_truth_one_situation hneg s s' hs hs'

-- If worldhood uses a tautology in place of obtaining, `Propn` is empty.
example (hw : TautologicalWorldhood actualWorld)
    (hneg : ∀ p : Propn, (actualWorld ⊨ ¬ₚ p) ↔ ¬ (actualWorld ⊨ p)) :
    Propn → False :=
  tautological_worldhood_empty hw hneg

-- Neither collapse needs an axiom beyond the inventory: the first uses
-- `Comprehension`, through the definition of `meet`, and
-- `abstract_extensionality`, through the extensionality of situations;
-- the second uses only `Comprehension`, through the definition of
-- `actualWorld`.
#print axioms classical_truth_one_situation
#print axioms tautological_worldhood_empty
