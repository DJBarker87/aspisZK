import Port8EFF_Bodies
import Port7CLEAN_Driver
import Port8EFF_Control

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
  | ok a =>
    simp only [returned,continueWith] at accepted ⊢
    exact ⟨a,rfl,accepted,rfl⟩

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
    ∃ p a after,
      Port6CK_Reader.reader reserved unwrap D ck proof pub .S2 hash=ok (.Ok (p,a)) ∧
      CheckpointBytes5Effect.run (VTop_Checkpoint.digest D) hash
        (Port8EFF_Bodies.readerCode reserved unwrap ck proof pub .S2) []=ok (.Ok (p,a),after) ∧
      (eval H (interpret (Port8EFF_Bodies.implementation ops reserved unwrap other)
        (Port8EFF_Control.commonTail D pub proof hash none (.Ok (p,a))))).2=ok (.Ok ()) ∧
      (eval H (interpret (Port8EFF_Bodies.implementation ops reserved unwrap other)
        (VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof ck hash none))).1=
        CheckpointBytes5Inputs.observe after ++
          (eval H (interpret (Port8EFF_Bodies.implementation ops reserved unwrap other)
            (Port8EFF_Control.commonTail D pub proof hash none (.Ok (p,a))))).1 := by
  rw [Port8EFF_Control.common_source] at accepted
  obtain ⟨out,returned,rest,logs⟩ := head _ _ _ H _ accepted
  rw [Port8EFF_Bodies.installed_reader,Port8EFF_Bodies.reader_value] at returned
  cases out with
  | Err e => rw [Port8EFF_Control.rejected] at rest; cases rest
  | Ok pair =>
    obtain ⟨p,a⟩ := pair
    obtain ⟨after,ran,full⟩ := Port8EFF_Bodies.reader_effects reserved unwrap D ck proof pub .S2 hash H oracle (.Ok (p,a)) returned
    refine ⟨p,a,after,returned,ran,rest,?_⟩
    rw [Port8EFF_Control.common_source,logs,Port8EFF_Bodies.installed_reader,full]

def authenticatedTail {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (pub proof ck : Slice U8)
    (r : core.result.Result transport.Variant verifier.Error) : Code (core.result.Result Unit verifier.Error) := do
  let cf ← VTop_Trace.liftResult (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | .Continue _ =>
    VTop_Trace.perform (.op13 none .Parsed)
    VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof ck hash none
  | .Break residual =>
    VTop_Trace.liftResult (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame verifier.Error) residual)

/-- Authentication's exact parser/mark prefix; the library mark emits no
reads. The accepted common body is reached on the same physical checkpoint. -/
theorem authenticated_common (ops : Ops) (reserved : Bool) (unwrap : Unwrap)
    (other : Implementation) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (pub proof ck : Slice U8) (H : Bytes → State)
    (accepted : (eval H (interpret (Port8EFF_Bodies.implementation ops reserved unwrap other)
      (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof ck hash none))).2=ok (.Ok ())) :
    (eval H (interpret (Port8EFF_Bodies.implementation ops reserved unwrap other)
      (VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof ck hash none))).2=ok (.Ok ()) ∧
    ∃ earlier, (eval H (interpret (Port8EFF_Bodies.implementation ops reserved unwrap other)
      (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof ck hash none))).1=
      earlier ++ (eval H (interpret (Port8EFF_Bodies.implementation ops reserved unwrap other)
        (VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof ck hash none))).1 := by
  let impl : Implementation := Port8EFF_Bodies.implementation ops reserved unwrap other
  let k := authenticatedTail D hash pub proof ck
  have shape : VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof ck hash none=
      .call (.op3 proof) k := rfl
  rw [shape] at accepted
  obtain ⟨parsed,called,rest,logs⟩ := head impl _ k H _ accepted
  cases parsed with
  | Err e => cases rest
  | Ok v =>
    let k1 : Unit → Code (core.result.Result Unit verifier.Error) := fun _ =>
      VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof ck hash none
    change (eval H (interpret impl (.call (.op13 none .Parsed) k1))).2=_ at rest
    obtain ⟨u,markCall,common,markLogs⟩ := head impl (.op13 none .Parsed) k1 H _ rest
    cases u
    refine ⟨common, (eval H (impl (.op3 proof))).1,?_⟩
    rw [shape,logs]
    change _ = _ ++ (eval H (interpret impl (k1 ()))).1
    change _ ++ (eval H (interpret impl (.call (.op13 none .Parsed) k1))).1 = _
    rw [markLogs]
    rfl

#print axioms authenticated_common
#print axioms head
#print axioms common_shape
#print axioms common_reader
end AspisR1.Port8EFF_Driver
end
