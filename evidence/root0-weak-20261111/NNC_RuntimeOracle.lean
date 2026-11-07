import NNC_FirstCuts
set_option autoImplicit false
noncomputable section
namespace NNC_RuntimeOracle
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Derive the writer's nested carrier interpretation from the SAME approved
syscall/digest extraction, rather than introduce an additional oracle law. -/
theorem writer {F C : Type} (c : DrvC_Installation.Configuration F C)
 (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
 (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
 (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
 (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
 (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
 CheckpointBytes5Inputs.Oracle
  (VTop_Checkpoint.digest (Tx1Q_Install.digest (DrvC_Installation.currentDigest c))) () H := by
 intro parts digest returned
 change (DrvC_Installation.sdk c).op43 () parts=ok digest at returned
 rw [extraction.digestSource,S2W_DigestExtraction.digest_eq_hashv] at returned
 exact (syscall.returningValue parts digest returned).trans (p1.realization _)
#print axioms writer
end NNC_RuntimeOracle
