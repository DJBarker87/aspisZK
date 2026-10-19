import WeightsFieldSuccess
import Stage2ResumeConcreteDecoderCanonicality
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1WeightsFieldCurrent.WeightsFieldConcreteCanonical
open AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality
/-- The exact generated selector, instantiated with the retained concrete
wide parser, can return only canonical values. Array byte identity is not
assumed, and the selector's source slice/overflow checks remain in the body. -/
theorem field_success_canonical (bytes : Slice U8) (i : Usize) (value : ReaderWide)
    (h : weights.field actualWideDecoder bytes i = .ok value) :
    readerWideCanonical value := by
  exact WeightsFieldSuccess.canonical actualWideDecoder readerWideCanonical
    actualWideDecoder_success_canonical bytes i value h
#print axioms field_success_canonical
end AspisR1WeightsFieldCurrent.WeightsFieldConcreteCanonical
