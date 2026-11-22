import Grounding.Ontology
import Grounding.AbstractObjects
import Situation.Derived

/--
  Extensionality of situations.

  Situations are fully determined by their propositional content.
  This was formerly postulated.  It now follows from the definition of
  situations as abstract objects encoding only propositional
  properties: situations that make the same propositions true encode
  the same properties, so `abstract_extensionality` identifies them.
-/
theorem situation_extensionality :
    ∀ s s' : World, ExtEq s s' → s = s' := by
  intro s s' ⟨hs, hs', h⟩
  have ho := situation_is_object s hs
  have ho' := situation_is_object s' hs'
  apply abstract_extensionality s s' hs.1 hs'.1
  intro F
  constructor
  · intro he
    obtain ⟨p, rfl⟩ := hs.2 F he
    exact (TrueIn_iff_Enc s' ho' p).mp ((h p).mp ((TrueIn_iff_Enc s ho p).mpr he))
  · intro he
    obtain ⟨p, rfl⟩ := hs'.2 F he
    exact (TrueIn_iff_Enc s ho p).mp ((h p).mpr ((TrueIn_iff_Enc s' ho' p).mpr he))
