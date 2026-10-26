import P6C_OnCuts
import GExp_FirstPair
import GExp_SecondPair
set_option autoImplicit false
noncomputable section
namespace AspisR1.P6C_Whole
open Aeneas Aeneas.Std Result SdkC_Source S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open DrvC_Installation

def firstCode {F C : Type} (c : Configuration F C) (hashv : Parts → Result Digest) (f : FirstCut) :=
  GExp_FirstPair.code
    (Tx2I_Install.install c.adapter
      (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base c.stageBase)
        c.reserved c.query c.geometry)) c.finish)
    c.currentBase (Tx2N_Execution.control (AuS1_Install.base c.stageBase)
      c.reserved c.query c.geometry) c.finish c.reserved c.query c.geometry c.boundaries c.std hashv f

def secondCode {F C : Type} (c : Configuration F C) (hashv : Parts → Result Digest) (s : SecondCut) :=
  GExp_SecondPair.code c.adapter c.currentBase (AuS1_Install.base c.stageBase) c.finish
    c.reserved c.query c.geometry c.boundaries c.std hashv s

/-- Full first/second source programs, not just the batch fragments. Every
issued preparation, Merkle, checkpoint and resume syscall in these logs is
successful, and the defined extension preserves their complete observations. -/
def SafePair {F C : Type} (c : Configuration F C) (hashv : Parts → Result Digest)
    (H : Bytes → State) (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut) : Prop :=
  P6C_Pair.Safe hashv H (firstCode c hashv f) (.Ok saved) ∧
  P6C_Pair.Safe hashv H (secondCode c hashv s) (.Ok ())

theorem same_cuts {F C : Type} (c : Configuration F C)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : Parts → Result Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (sdk c) accounts1 accounts2 saved f s) :
    SafePair c hashv H saved f s := by
  have first := GExp_FirstPair.same_pair
    (Tx2I_Install.install c.adapter
      (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base c.stageBase)
        c.reserved c.query c.geometry)) c.finish)
    c.currentBase (Tx2N_Execution.control (AuS1_Install.base c.stageBase)
      c.reserved c.query c.geometry) c.finish c.reserved c.query c.geometry c.boundaries c.std
    native1 native2 hashv extraction sha256 H p1 syscall accounts1 accounts2 saved f s cuts
  have second := GExp_SecondPair.same_pair c.adapter c.currentBase (AuS1_Install.base c.stageBase)
    c.finish c.reserved c.query c.geometry c.boundaries c.std native1 native2 hashv extraction
    sha256 H p1 syscall accounts1 accounts2 saved f s cuts
  exact ⟨P6C_Pair.safe hashv H _ _ first,P6C_Pair.safe hashv H _ _ second⟩

#print axioms same_cuts
end AspisR1.P6C_Whole
end
