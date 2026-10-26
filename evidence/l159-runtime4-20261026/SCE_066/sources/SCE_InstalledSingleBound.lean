import SCE_SingleBound
import SCE_SubmissionBound
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_InstalledSingleBound
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_ByteCarrier SCE_Experiment

/-- Actual installed source pair, WITHOUT runtime binding or a separate P
query hypothesis. Its source runtime is explicitly not the account observer. -/
theorem source_bound {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (raw : F3T_CanonicalJoin.AcceptedVerifierJoin c D (F3T_Installed.source c hashv))
    (a : Adversary A) (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0) :
    F3T_RuntimeBound.failureModel (SCE_SingleRuntime.runtime c (F3T_Installed.source c hashv)
      (submission a)) ≤ StartChargeNumeric.totalBound (Q0+Q1) := by
  exact SCE_SingleBound.source_failure_bound c D _ (F3T_Installed.physical c hashv) raw
    (submission a) (Q0+Q1) (SCE_SubmissionBound.queries a Q0 Q1 prefixBound)

#print axioms source_bound
end AspisR1.SCE_InstalledSingleBound
end
