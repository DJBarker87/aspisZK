import SCE_InstalledSingleBound
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_SingleNumerical
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw
open F3T_ByteCarrier SCE_Experiment
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (raw : F3T_CanonicalJoin.AcceptedVerifierJoin c D (F3T_Installed.source c hashv))
    (a : Adversary A)
/-- Numerical source-pair consequence, not an adaptive-account theorem. -/
theorem zero (prefix : ∀ H, (eval H a.first).1.length ≤ 0) :
    F3T_RuntimeBound.failureModel (SCE_SingleRuntime.runtime c (F3T_Installed.source c hashv)
      (submission a)) ≤ 1/(2:Rat)^100 :=
  (SCE_InstalledSingleBound.source_bound c D hashv raw a 0 0 prefix).trans StartChargeNumeric.zero_queries

theorem per_attempt (Q0 Q1 : Nat) (prefix : ∀ H, (eval H a.first).1.length ≤ Q0)
    (range : Q0+Q1 ≤ OraclePortHeadlineFrozen2.Qmax) :
    F3T_RuntimeBound.failureModel (SCE_SingleRuntime.runtime c (F3T_Installed.source c hashv)
      (submission a)) ≤ (Q0+Q1+1:Rat)*(1/(2:Rat)^100) := by
  exact (SCE_InstalledSingleBound.source_bound c D hashv raw a Q0 Q1 prefix).trans
    (StartChargeNumeric.safe_range (Q0+Q1) range)
#print axioms zero
#print axioms per_attempt
end AspisR1.SCE_SingleNumerical
end
