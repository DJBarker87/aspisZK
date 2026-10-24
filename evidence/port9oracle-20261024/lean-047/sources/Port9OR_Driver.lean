import Port9OR_Bridge
import Port7CLEAN_Driver
import Port8EFF_Control

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_Driver
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
    (accepted : (eval H (interpret (Port9OR_Bodies.implementation ops reserved unwrap other)
      (VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof ck hash none))).2=ok (.Ok ())) :
    ∃ p a after,
      Port6CK_Reader.reader reserved unwrap (Port9OR_Bodies.native D H) ck proof pub .S2 hash=ok (.Ok (p,a)) ∧
      CheckpointBytes5Effect.run (VTop_Checkpoint.digest (Port9OR_Bodies.native D H)) hash
        (Port8EFF_Bodies.readerCode reserved unwrap ck proof pub .S2) []=ok (.Ok (p,a),after) ∧
      (eval H (interpret (Port9OR_Bodies.implementation ops reserved unwrap other)
        (Port8EFF_Control.commonTail D pub proof hash none (.Ok (p,a))))).2=ok (.Ok ()) ∧
      (eval H (interpret (Port9OR_Bodies.implementation ops reserved unwrap other)
        (VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof ck hash none))).1=
        CheckpointBytes5Inputs.observe after ++
          (eval H (interpret (Port9OR_Bodies.implementation ops reserved unwrap other)
            (Port8EFF_Control.commonTail D pub proof hash none (.Ok (p,a))))).1 := by
  rw [Port8EFF_Control.common_source] at accepted
  obtain ⟨out,returned,rest,logs⟩ := head _ _ _ H _ accepted
  rw [Port9OR_Bodies.installed_reader] at returned
  have nativeReturned := (Port9OR_Bodies.reader_value reserved unwrap D ck proof pub .S2 hash H).symm.trans returned
  cases out with
  | Err e => rw [Port8EFF_Control.rejected] at rest; cases rest
  | Ok pair =>
    obtain ⟨p,a⟩ := pair
    obtain ⟨after,ran,full⟩ := Port9OR_Bridge.reader_success reserved unwrap D ck proof pub .S2 hash H (.Ok (p,a)) returned
    refine ⟨p,a,after,nativeReturned,ran,rest,?_⟩
    rw [Port8EFF_Control.common_source,logs,Port9OR_Bodies.installed_reader,full]

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
    (accepted : (eval H (interpret (Port9OR_Bodies.implementation ops reserved unwrap other)
      (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof ck hash none))).2=ok (.Ok ())) :
    (eval H (interpret (Port9OR_Bodies.implementation ops reserved unwrap other)
      (VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof ck hash none))).2=ok (.Ok ()) ∧
    ∃ earlier, (eval H (interpret (Port9OR_Bodies.implementation ops reserved unwrap other)
      (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof ck hash none))).1=
      earlier ++ (eval H (interpret (Port9OR_Bodies.implementation ops reserved unwrap other)
        (VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof ck hash none))).1 := by
  let impl : Implementation := Port9OR_Bodies.implementation ops reserved unwrap other
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

/-- Exact second powers operand from current18's returned Prepared. The
returned g, not an independently chosen array, feeds the query continuation. -/
theorem powers_reached (ops : Ops) (reserved : Bool) (unwrap : Unwrap)
    (other : Implementation) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (pub proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (H : Bytes → State)
    (accepted : (eval H (interpret (Port9OR_Bodies.implementation ops reserved unwrap other)
      (Port8EFF_Control.commonTail D pub proof hash none (.Ok (p,a))))).2=ok (.Ok ())) :
    a.next=10#usize ∧ ∃ g,
      (eval H (other (.op17 29#usize p.gamma))).2=ok g ∧
      (eval H (interpret (Port9OR_Bodies.implementation ops reserved unwrap other)
        (Port8EFF_Control.afterPowers D proof hash none p a 10#usize g))).2=ok (.Ok ()) := by
  let impl : Implementation := Port9OR_Bodies.implementation ops reserved unwrap other
  rw [Port8EFF_Control.common_ok] at accepted
  obtain ⟨i,called,rest,logs⟩ := head impl .op16 _ H _ accepted
  have same : (10#usize : Usize)=i := Result.ok.inj called
  subst i
  by_cases next : a.next=10#usize
  · refine ⟨next,?_⟩
    simp only [Port8EFF_Control.afterSplit,next,bne_self_eq_false,Bool.false_eq_true,if_false] at rest
    obtain ⟨g,returned,continuation,_⟩ := head impl (.op17 29#usize p.gamma) _ H _ rest
    exact ⟨g,returned,continuation⟩
  · have bad : (a.next != 10#usize)=true := by simpa only [bne_iff_ne] using next
    simp only [Port8EFF_Control.afterSplit,bad,if_true,interpret,eval] at rest
    cases rest

#print axioms powers_reached

/-- On the first source record, the accepted driver uses TX1's exact saved
Vec for current18. Its complete reader observations occur chronologically
between actual earlier and later driver observations. -/
theorem first_reader (decoder : LiteralByteProtocol.Decoder)
    (adapter : AdapterRw.Ops) (ops : Ops) (reserved : Bool) (unwrap : Unwrap)
    (other : Implementation) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (P : Port1_StoredCarrier.ByteProver) (H : Bytes → State)
    (accepted : (eval H (Port6AUTH_Prefix.source decoder
      (Port1_Driver.rust adapter (Port9OR_Bodies.implementation ops reserved unwrap other) D hash) P)).2.2=true) :
    let impl : Implementation := Port9OR_Bodies.implementation ops reserved unwrap other
    let rust := Port1_Driver.rust adapter impl D hash
    let input := (Port6AUTH_SourceCut.first rust P H).2.1
    ∃ pub proof semantic saved p a after earlier,
      Port1_Driver.asSlice input.statement.pubBytes=some pub ∧
      Port1_Driver.asSlice input.stored=some proof ∧
      Port1_Driver.decodeSemantic adapter pub=ok (some semantic) ∧
      (eval H (interpret impl (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))).2=ok (.Ok saved) ∧
      Port6CK_Reader.reader reserved unwrap (Port9OR_Bodies.native D H) saved.deref proof pub .S2 hash=ok (.Ok (p,a)) ∧
      CheckpointBytes5Effect.run (VTop_Checkpoint.digest (Port9OR_Bodies.native D H)) hash
        (Port8EFF_Bodies.readerCode reserved unwrap saved.deref proof pub .S2) []=ok (.Ok (p,a),after) ∧
      (eval H (interpret impl (Port8EFF_Control.commonTail D pub proof hash none (.Ok (p,a))))).2=ok (.Ok ()) ∧
      (eval H (rust input)).1=earlier ++ CheckpointBytes5Inputs.observe after ++
        (eval H (interpret impl (Port8EFF_Control.commonTail D pub proof hash none (.Ok (p,a))))).1 := by
  let impl : Implementation := Port9OR_Bodies.implementation ops reserved unwrap other
  let rust := Port1_Driver.rust adapter impl D hash
  let input := (Port6AUTH_SourceCut.first rust P H).2.1
  have first := Port7CLEAN_Driver.first_accepted decoder adapter impl D hash P H accepted
  obtain ⟨pub,proof,semantic,hpub,hproof,decoded,stages⟩ :=
    Port7CLEAN_Driver.accepted_entry adapter impl D hash input H first
  obtain ⟨saved,tx1,tx2,stageLogs⟩ := Port7CLEAN_Driver.accepted_stages impl D hash semantic pub proof H stages
  obtain ⟨common,authEarlier,authLogs⟩ := authenticated_common ops reserved unwrap other D hash pub proof saved.deref H tx2
  obtain ⟨p,a,after,resumed,ran,rest,commonLogs⟩ := common_reader ops reserved unwrap other D hash pub proof saved.deref H common
  refine ⟨pub,proof,semantic,saved,p,a,after,
    (eval H (interpret impl (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))).1 ++ authEarlier,
    hpub,hproof,decoded,tx1,resumed,ran,rest,?_⟩
  change (eval H (Port1_Driver.rust adapter impl D hash input)).1=_
  simp only [Port1_Driver.rust,hpub,hproof,decoded]
  rw [stageLogs,authLogs,commonLogs]
  simp only [List.append_assoc]
  rfl

#print axioms first_reader
#print axioms authenticated_common
#print axioms head
#print axioms common_shape
#print axioms common_reader
end AspisR1.Port9OR_Driver
end
