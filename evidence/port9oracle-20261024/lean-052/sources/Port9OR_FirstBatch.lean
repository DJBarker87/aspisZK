import Port9OR_Reached

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_FirstBatch
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Actual restored p.gamma powers return and its exact log segment before
batch1. This is source continuation composition, not a native powers proof. -/
theorem powers_logs (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator) (H : Bytes → State)
    (accepted : (eval H (interpret (Port9OR_Installed.implementation ops reserved unwrap rest)
      (Port8EFF_Control.commonTail D pub proof hash none (.Ok (p,a))))).2=ok (.Ok ())) :
    a.next=10#usize ∧ ∃ g,
      (eval H (rest (.op17 29#usize p.gamma))).2=ok g ∧
      (eval H (interpret (Port9OR_Installed.implementation ops reserved unwrap rest)
        (Port8EFF_Control.afterPowers D proof hash none p a 10#usize g))).2=ok (.Ok ()) ∧
      (eval H (interpret (Port9OR_Installed.implementation ops reserved unwrap rest)
        (Port8EFF_Control.commonTail D pub proof hash none (.Ok (p,a))))).1=
        (eval H (rest (.op17 29#usize p.gamma))).1 ++
        (eval H (interpret (Port9OR_Installed.implementation ops reserved unwrap rest)
          (Port8EFF_Control.afterPowers D proof hash none p a 10#usize g))).1 := by
  let impl : Implementation := Port9OR_Installed.implementation ops reserved unwrap rest
  rw [Port8EFF_Control.common_ok] at accepted ⊢
  obtain ⟨i,called,remaining,logs⟩ := Port9OR_Driver.head impl .op16 _ H _ accepted
  have same : (10#usize : Usize)=i := Result.ok.inj called
  subst i
  by_cases next : a.next=10#usize
  · simp only [Port8EFF_Control.afterSplit,next,bne_self_eq_false,Bool.false_eq_true,if_false] at remaining
    obtain ⟨g,returned,continuation,powerLogs⟩ := Port9OR_Driver.head impl (.op17 29#usize p.gamma) _ H _ remaining
    refine ⟨next,g,returned,continuation,?_⟩
    rw [logs]
    simp only [Port8EFF_Control.afterSplit,next,bne_self_eq_false,Bool.false_eq_true,if_false]
    rw [powerLogs]
    rfl
  · have bad : (a.next != 10#usize)=true := by simpa only [bne_iff_ne] using next
    simp only [Port8EFF_Control.afterSplit,bad,if_true,interpret,eval] at remaining
    cases remaining

/-- Accepted FIRST actual source record supplies TX1's saved checkpoint,
current18's SAME p/a, its actual powers operand/return and reached physical
batch1 root, with the full batch observation embedded in the driver log. -/
theorem first_batch (decoder : LiteralByteProtocol.Decoder) (adapter : AdapterRw.Ops)
    (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap) (rest : Implementation)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (P : Port1_StoredCarrier.ByteProver) (H : Bytes → State)
    (accepted : (eval H (Port6AUTH_Prefix.source decoder
      (Port1_Driver.rust adapter (Port9OR_Installed.implementation ops reserved unwrap rest) D hash) P)).2.2=true) :
    let impl : Implementation := Port9OR_Installed.implementation ops reserved unwrap rest
    let rust := Port1_Driver.rust adapter impl D hash
    let input := (Port6AUTH_SourceCut.first rust P H).2.1
    ∃ pub proof semantic saved p a g folded earlier later,
      Port1_Driver.asSlice input.statement.pubBytes=some pub ∧
      Port1_Driver.asSlice input.stored=some proof ∧
      Port1_Driver.decodeSemantic adapter pub=ok (some semantic) ∧
      (eval H (interpret impl (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))).2=ok (.Ok saved) ∧
      Port6CK_Reader.reader reserved unwrap (Port9OR_Bodies.native D H) saved.deref proof pub .S2 hash=ok (.Ok (p,a)) ∧
      a.next=10#usize ∧ (eval H (rest (.op17 29#usize p.gamma))).2=ok g ∧
      Port4B_Install.batch (Port9OR_Bodies.native D H) proof p folded 1#usize hash=ok (.Ok ()) ∧
      (eval H (rust input)).1=earlier ++
        (eval H (Port9OR_Installed.batch D hash proof p folded 1#usize)).1 ++ later := by
  let impl : Implementation := Port9OR_Installed.implementation ops reserved unwrap rest
  let rust := Port1_Driver.rust adapter impl D hash
  let input := (Port6AUTH_SourceCut.first rust P H).2.1
  obtain ⟨pub,proof,semantic,saved,p,a,after,earlier,hpub,hproof,decoded,tx1,resumed,ran,remaining,logs⟩ :=
    Port9OR_Driver.first_reader decoder adapter ops reserved unwrap (Port9OR_Installed.other rest) D hash P H accepted
  obtain ⟨next,g,powered,powers,powerLogs⟩ := powers_logs ops reserved unwrap rest D hash pub proof p a H remaining
  obtain ⟨inactive,folded,slice,conversion,read,array,unwrapped,batch,suffix,batchLogs⟩ :=
    Port9OR_Reached.after_powers ops reserved unwrap rest D hash proof p a 10#usize g H powers
  refine ⟨pub,proof,semantic,saved,p,a,g,folded,
    earlier ++ CheckpointBytes5Inputs.observe after ++ (eval H (rest (.op17 29#usize p.gamma))).1,
    _,hpub,hproof,decoded,tx1,resumed,next,powered,batch,?_⟩
  rw [logs,powerLogs,batchLogs]
  simp only [List.append_assoc]
  all_goals rfl

#print axioms powers_logs
#print axioms first_batch
end AspisR1.Port9OR_FirstBatch
end
