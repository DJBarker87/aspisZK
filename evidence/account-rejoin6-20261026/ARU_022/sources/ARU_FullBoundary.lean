import P6C_FullBoundary
import ARU_Whole
import ARU_Issued
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_FullBoundary
open Aeneas Aeneas.Std Result SdkC_Source S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open DrvC_Installation MultiproofConePhysicalTransport P6C_FullBoundary
theorem same_cuts {F C : Type} (c : Configuration F C)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : Parts → Result Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdk c) native1 native2 hashv)
    (H : Bytes → State)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (sdk c) accounts1 accounts2 saved f s)
    (firstAgrees : ARS_QueryTransport.Agrees H (firstLog c hashv f))
    (secondAgrees : ARS_QueryTransport.Agrees H (secondLog c hashv s)) :
    Facts c hashv H saved f s := by
  have safe := ARU_Whole.same_cuts c native1 native2 hashv extraction H
    accounts1 accounts2 saved f s cuts firstAgrees secondAgrees
  have first := ARU_Issued.derive hashv H
    (P6C_Whole.firstCode c hashv f) (.Ok saved) safe.1.1.1 firstAgrees
  have second := ARU_Issued.derive hashv H
    (P6C_Whole.secondCode c hashv s) (.Ok ()) safe.2.1.1 secondAgrees
  refine ⟨safe,first,second,?_⟩
  intro q member
  rcases List.mem_append.mp member with left | right
  · exact P6C_Issued.installed _ native1 native2 hashv extraction H _ first q left
  · exact P6C_Issued.installed _ native1 native2 hashv extraction H _ second q right

#print axioms same_cuts
end AspisR1.ARU_FullBoundary
end
