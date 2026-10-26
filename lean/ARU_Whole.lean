import P6C_Whole
import ARU_FirstPair
import ARU_SecondPair
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_Whole
open Aeneas Aeneas.Std Result SdkC_Source S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open DrvC_Installation P6C_Whole
theorem same_cuts {F C : Type} (c : Configuration F C)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : Parts → Result Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdk c) native1 native2 hashv)
    (H : Bytes → State)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (sdk c) accounts1 accounts2 saved f s)
    (firstAgrees : ARS_QueryTransport.Agrees H (run hashv (firstCode c hashv f) []).2)
    (secondAgrees : ARS_QueryTransport.Agrees H (run hashv (secondCode c hashv s) []).2) :
    SafePair c hashv H saved f s := by
  have first := ARU_FirstPair.same_pair
    (Tx2I_Install.install c.adapter
      (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base c.stageBase)
        c.reserved c.query c.geometry)) c.finish)
    c.currentBase (Tx2N_Execution.control (AuS1_Install.base c.stageBase)
      c.reserved c.query c.geometry) c.finish c.reserved c.query c.geometry c.boundaries c.std
    native1 native2 hashv extraction H accounts1 accounts2 saved f s cuts firstAgrees
  have second := ARU_SecondPair.same_pair c.adapter c.currentBase (AuS1_Install.base c.stageBase)
    c.finish c.reserved c.query c.geometry c.boundaries c.std native1 native2 hashv extraction
    H accounts1 accounts2 saved f s cuts secondAgrees
  exact ⟨P6C_Pair.safe hashv H _ _ first,P6C_Pair.safe hashv H _ _ second⟩

#print axioms same_cuts
end AspisR1.ARU_Whole
end
