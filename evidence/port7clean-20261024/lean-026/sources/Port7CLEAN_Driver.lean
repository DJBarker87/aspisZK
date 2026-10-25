import Port1_Driver
import Port1_Annotation
import Port6AUTH_SourceCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port7CLEAN_Driver
open Aeneas Aeneas.Std Result VTop_Stages VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Accepted driver stages expose the actual saved checkpoint and both
successes, with exact chronological logs. No independent TX2 run is chosen. -/
theorem accepted_stages (impl : Implementation) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (semantic : Port1_Driver.Semantic)
    (pub proof : Slice U8) (H : Bytes → State)
    (accepted : (eval H (Port1_Driver.stages impl D hash semantic pub proof)).2=true) :
    ∃ saved : alloc.vec.Vec U8,
      (eval H (interpret impl (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))).2=ok (.Ok saved) ∧
      (eval H (interpret impl (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof saved.deref hash none))).2=ok (.Ok ()) ∧
      (eval H (Port1_Driver.stages impl D hash semantic pub proof)).1=
        (eval H (interpret impl (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))).1 ++
        (eval H (interpret impl (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof saved.deref hash none))).1 := by
  unfold Port1_Driver.stages at accepted ⊢
  simp only [eval_bind] at accepted ⊢
  cases first : (eval H (interpret impl
    (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))).2 with
  | fail e => simp only [first,eval,Bool.false_eq_true] at accepted
  | div => simp only [first,eval,Bool.false_eq_true] at accepted
  | ok result =>
    cases result with
    | Err e => simp only [first,eval,Bool.false_eq_true] at accepted
    | Ok saved =>
      simp only [first,eval_bind,eval,List.append_nil] at accepted ⊢
      cases second : (eval H (interpret impl
        (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof saved.deref hash none))).2 with
      | fail e => simp only [second,Port1_Driver.verdict,Bool.false_eq_true] at accepted
      | div => simp only [second,Port1_Driver.verdict,Bool.false_eq_true] at accepted
      | ok result =>
        cases result with
        | Err e => simp only [second,Port1_Driver.verdict,Bool.false_eq_true] at accepted
        | Ok value => cases value; exact ⟨saved,rfl,second,rfl⟩

/-- Accepted physical entry exposes its exact decoded public/proof slices. -/
theorem accepted_entry (adapter : AdapterRw.Ops) (impl : Implementation) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (i : OraclePortStoredExperimentC4.Input) (H : Bytes → State)
    (accepted : (eval H (Port1_Driver.rust adapter impl D hash i)).2=true) :
    ∃ pub proof semantic,
      Port1_Driver.asSlice i.statement.pubBytes=some pub ∧
      Port1_Driver.asSlice i.stored=some proof ∧
      Port1_Driver.decodeSemantic adapter pub=ok (some semantic) ∧
      (eval H (Port1_Driver.stages impl D hash semantic pub proof)).2=true := by
  cases pub : Port1_Driver.asSlice i.statement.pubBytes with
  | none => simp only [Port1_Driver.rust,pub,eval,Bool.false_eq_true] at accepted
  | some publicBytes =>
    cases proof : Port1_Driver.asSlice i.stored with
    | none => simp only [Port1_Driver.rust,pub,proof,eval,Bool.false_eq_true] at accepted
    | some proofBytes =>
      cases semantic : Port1_Driver.decodeSemantic adapter publicBytes with
      | fail e => simp only [Port1_Driver.rust,pub,proof,semantic,eval,Bool.false_eq_true] at accepted
      | div => simp only [Port1_Driver.rust,pub,proof,semantic,eval,Bool.false_eq_true] at accepted
      | ok result =>
        cases result with
        | none => simp only [Port1_Driver.rust,pub,proof,semantic,eval,Bool.false_eq_true] at accepted
        | some value =>
          exact ⟨publicBytes,proofBytes,value,rfl,rfl,semantic,
            by simpa only [Port1_Driver.rust,pub,proof,semantic] using accepted⟩

/-- Source acceptance refers to the first source record's SAME physical
bytes. The second annotation pass cannot choose another checkpoint path. -/
theorem first_accepted (decoder : LiteralByteProtocol.Decoder)
    (adapter : AdapterRw.Ops) (impl : Implementation) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (P : Port1_StoredCarrier.ByteProver) (H : Bytes → State)
    (accepted : (eval H (Port6AUTH_Prefix.source decoder
      (Port1_Driver.rust adapter impl D hash) P)).2.2=true) :
    (eval H (Port1_Driver.rust adapter impl D hash
      (Port6AUTH_SourceCut.first (Port1_Driver.rust adapter impl D hash) P H).2.1)).2=true := by
  simpa only [Port6AUTH_Prefix.source_eval,OraclePortFrozen2Join.annotatedWith_eval,
    OraclePortStoredExperimentC4.view,Port1_Annotation.source_enrich] using accepted

#print axioms accepted_entry
#print axioms first_accepted

#print axioms accepted_stages
end AspisR1.Port7CLEAN_Driver
end
