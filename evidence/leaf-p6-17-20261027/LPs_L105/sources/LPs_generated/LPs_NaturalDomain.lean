import LPq_ExpandedWords
import LPq_CarrierFacts
import LPr_SelectedWords
set_option autoImplicit false
namespace AspisR1.LPs_NaturalDomain
open Aeneas Aeneas.Std Result

/-- Nominal application of the inherited LPr byte/word ports to LPq. The
check/expand producer cannot yet co-import with this consumer; its facts
remain explicit here rather than being credited as a discharged native join. -/
theorem selected (compact y1 : Slice U8) (len : y1.val.length=928)
    (expanded : LPq_ExpandedWords.Expanded compact.val y1.val)
    (canonical : LPq_ExpandedWords.CompactCanonical compact.val) :
    LPq_SelectedDomain.ByteDomain y1 := by
  apply LPr_SelectedWords.selected_words y1 len
  intro row j hr hj
  exact LPq_ExpandedWords.canonical compact.val y1.val expanded canonical row j hr hj

#print axioms selected
end AspisR1.LPs_NaturalDomain
