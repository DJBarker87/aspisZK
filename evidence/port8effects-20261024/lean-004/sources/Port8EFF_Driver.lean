import Port8EFF_Bodies
import Port7CLEAN_Driver

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port8EFF_Driver
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open Port6CK_Semantic (Unwrap)

/-- Symbolic head cut retaining the dependent return and exact chronology. -/
theorem head {A B : Type} (impl : Implementation) (call : Call A) (k : A → Code B)
    (H : Bytes → State) (out : B)
    (accepted : (eval H (interpret impl (.call call k))).2=ok out) :
    ∃ a, (eval H (impl call)).2=ok a ∧
      (eval H (interpret impl (k a))).2=ok out ∧
      (eval H (interpret impl (.call call k))).1=
        (eval H (impl call)).1 ++ (eval H (interpret impl (k a))).1 := by
  simp only [interpret,eval_bind] at accepted ⊢
  cases returned : (eval H (impl call)).2 with
  | fail e => simp only [returned,continueWith,eval] at accepted; cases accepted
  | div => simp only [returned,continueWith,eval] at accepted; cases accepted
  | ok a => exact ⟨a,rfl,accepted,by simp only [continueWith]⟩

/-- The op18 continuation is the actual emitted TX2 continuation. -/
theorem common_shape {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (pub proof ck : Slice U8) :
    ∃ k, VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof ck hash none=
      .call (.op18 D ck proof pub .S2 hash) k := by exact ⟨_,rfl⟩

/-- Concrete owned reader, exact returned pair/error and complete current
reader effects occur at the beginning of this accepted common continuation.
The next continuation consumes that SAME return; no replacement pair is used. -/
theorem common_reader (ops : Ops) (reserved : Bool) (unwrap : Unwrap)
    (other : Implementation) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (pub proof ck : Slice U8) (H : Bytes → State)
    (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest D) hash H)
    (accepted : (eval H (interpret (Port8EFF_Bodies.implementation ops reserved unwrap other)
      (VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof ck hash none))).2=ok (.Ok ())) :
    ∃ out k after,
      VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof ck hash none=
        .call (.op18 D ck proof pub .S2 hash) k ∧
      Port6CK_Reader.reader reserved unwrap D ck proof pub .S2 hash=ok out ∧
      CheckpointBytes5Effect.run (VTop_Checkpoint.digest D) hash
        (Port8EFF_Bodies.readerCode reserved unwrap ck proof pub .S2) []=ok (out,after) ∧
      (eval H (interpret (Port8EFF_Bodies.implementation ops reserved unwrap other) (k out))).2=ok (.Ok ()) ∧
      (eval H (interpret (Port8EFF_Bodies.implementation ops reserved unwrap other)
        (VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof ck hash none))).1=
        CheckpointBytes5Inputs.observe after ++
          (eval H (interpret (Port8EFF_Bodies.implementation ops reserved unwrap other) (k out))).1 := by
  obtain ⟨k,shape⟩ := common_shape D hash pub proof ck
  rw [shape] at accepted
  obtain ⟨out,returned,rest,logs⟩ := head _ _ k H _ accepted
  rw [Port8EFF_Bodies.installed_reader,Port8EFF_Bodies.reader_value] at returned
  obtain ⟨after,ran,full⟩ := Port8EFF_Bodies.reader_effects reserved unwrap D ck proof pub .S2 hash H oracle out returned
  refine ⟨out,k,after,shape,returned,ran,rest,?_⟩
  rw [shape,logs,Port8EFF_Bodies.installed_reader,full]

#print axioms head
#print axioms common_shape
#print axioms common_reader
end AspisR1.Port8EFF_Driver
end
