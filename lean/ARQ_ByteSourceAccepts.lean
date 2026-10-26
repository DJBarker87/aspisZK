import F3T_Installed
import SCE_FirstCutBytes
import SCE_SubmissionExt
import DrvC_SourceEntry
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_ByteSourceAccepts
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment F3T_ByteCarrier S2W_NativeConsolidation

/-- Original submission association transports an actual accepted driver
input to precisely F3X's physical/stored carrier. No model acceptance or log
equality is used. The installed driver's source equality remains explicit. -/
theorem accepted {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (driver : OraclePortStoredExperimentC4.Input → Program Bytes State Bool)
    (installed : driver = DrvC_SourceEntry.source c hashv)
    (a : Adversary A) (H : Bytes → State) (accounts2 : S2W_ExtractionBoundary.Accounts)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (DrvC_Installation.sdk c) (eval H a.first).2.entry.first accounts2 saved f s)
    (i : OraclePortStoredExperimentC4.Input)
    (pub : i.statement.pubBytes = bytesOf f.pub.val) (proof : i.stored = bytesOf f.proof.val)
    (yes : (eval H (driver i)).2 = true) :
    (eval H (F3T_Installed.source c hashv (input c (eval H (submission a)).2))).2 = true := by
  have b := SCE_FirstCutBytes.submitted_cut (eval H a.first).2 _ accounts2 saved f s cuts
  rw [submission_eval]
  rw [F3T_Installed.old_source c hashv _ i (b.1.trans pub.symm) (b.2.trans proof.symm),←installed]
  exact yes

#print axioms accepted
end AspisR1.ARQ_ByteSourceAccepts
end
