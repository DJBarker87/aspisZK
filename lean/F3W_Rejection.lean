import F3T_ByteCarrier
import F3K_SamplerProtocol
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3W_Rejection
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open F3T_ByteCarrier

/-- The complete model samples before its decision, even on malformed bytes. -/
theorem model_log_nonempty (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (i : F3_Model.Input) : (eval H (F3_Model.verifier D i)).1≠[] := by
  have reads := LiteralByteProtocol.chainsRead D (fun _ _=>none) 0 (FS.emptyPrefix i.semantic.value) (i.proof 0) (by change 0<33;decide)
  change firstCell (LiteralByteSampler.samp 0 (FS.emptyPrefix i.semantic.value) (i.proof 0))≠none at reads
  change (eval H (OracleDecisionFeasibilityCore.verifierFrom D _ i.proof 33
    (FS.emptyPrefix i.semantic.value))).1≠[]
  rw [OracleDecisionFeasibilityCore.verifierFrom,eval_bind]
  cases sample : LiteralByteSampler.samp 0 (FS.emptyPrefix i.semantic.value) (i.proof 0) with
  | done a => simp only [sample,firstCell,ne_eq,not_true_eq_false] at reads
  | ask a k =>
    simp only [Sampler.toProgram,eval,List.cons_append]
    intro impossible;cases impossible
  | multi a cs nd k =>
    simp only [Sampler.toProgram,eval,List.cons_append]
    intro impossible;cases impossible

/-- Symbolic length rejection: no concrete enormous byte list is evaluated. -/
theorem oversized_eval {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest)
    (s : Submission) (large : Aeneas.Std.Usize.max<s.publicBytes.length) (H : Bytes → State) :
    eval H (F3T_Installed.source c hashv (input c s))=([],false) := by
  have unrepresentable : Port1_Driver.asSlice s.publicBytes=none := by
    simp only [Port1_Driver.asSlice,dif_neg (Nat.not_le.mpr large)]
  simp only [F3T_Installed.source,input,unrepresentable,eval]

theorem oversized_ne {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest)
    (s : Submission) (large : Aeneas.Std.Usize.max<s.publicBytes.length)
    (D : LiteralByteProtocol.Decoder) (H : Bytes → State) :
    eval H (F3T_Installed.source c hashv (input c s))≠eval H (F3_Model.verifier D (input c s)) := by
  intro equal
  have empty := congrArg Prod.fst equal
  rw [oversized_eval c hashv s large H] at empty
  exact model_log_nonempty D H (input c s) empty.symm

#print axioms model_log_nonempty
#print axioms oversized_eval
#print axioms oversized_ne
end AspisR1.F3W_Rejection
end
