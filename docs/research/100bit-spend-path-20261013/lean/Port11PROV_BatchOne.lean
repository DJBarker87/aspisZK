import Port9OR_FirstBatch
import Port11PROV_Views
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port11PROV_BatchOne
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Accepted FIRST actual source record supplies TX1's saved checkpoint,
current18's SAME p/a, its actual powers operand/return and reached physical
batch1 root, with the full batch observation embedded in the driver log. -/
theorem reached (decoder : LiteralByteProtocol.Decoder) (adapter : AdapterRw.Ops)
    (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap) (rest : Implementation)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (P : Port1_StoredCarrier.ByteProver) (H : Bytes → State)
    (accepted : (eval H (Port6AUTH_Prefix.source decoder
      (Port1_Driver.rust adapter (Port9OR_Installed.implementation ops reserved unwrap rest) D hash) P)).2.2=true) :
    let impl : Implementation := Port9OR_Installed.implementation ops reserved unwrap rest
    let rust := Port1_Driver.rust adapter impl D hash
    let input := (Port6AUTH_SourceCut.first rust P H).2.1
    ∃ pub proof semantic saved p a g folded slice conversion earlier later,
      Port1_Driver.asSlice input.statement.pubBytes=some pub ∧
      Port1_Driver.asSlice input.stored=some proof ∧
      Port1_Driver.decodeSemantic adapter pub=ok (some semantic) ∧
      (eval H (interpret impl (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))).2=ok (.Ok saved) ∧
      Port6CK_Reader.reader reserved unwrap (Port9OR_Bodies.native D H) saved.deref proof pub .S2 hash=ok (.Ok (p,a)) ∧
      a.next=10#usize ∧ (eval H (rest (.op17 29#usize p.gamma))).2=ok g ∧
      Port4B_Install.batch (Port9OR_Bodies.native D H) proof p folded 1#usize hash=ok (.Ok ()) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proof
        {start:=7751#usize,«end»:=7783#usize}=ok slice ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 slice=ok conversion ∧
      ops.unwrap32 conversion=ok folded ∧
      (eval H (rust input)).1=earlier ++
        (eval H (Port9OR_Installed.batch D hash proof p folded 1#usize)).1 ++ later := by
  let impl : Implementation := Port9OR_Installed.implementation ops reserved unwrap rest
  let rust := Port1_Driver.rust adapter impl D hash
  let input := (Port6AUTH_SourceCut.first rust P H).2.1
  obtain ⟨pub,proof,semantic,saved,p,a,after,earlier,hpub,hproof,decoded,tx1,resumed,ran,remaining,logs⟩ :=
    Port9OR_Driver.first_reader decoder adapter ops reserved unwrap (Port9OR_Installed.other rest) D hash P H accepted
  obtain ⟨next,g,powered,powers,powerLogs⟩ := Port9OR_FirstBatch.powers_logs ops reserved unwrap rest D hash pub proof p a H remaining
  obtain ⟨inactive,folded,slice,conversion,read,array,unwrapped,batch,suffix,batchLogs⟩ :=
    Port9OR_Reached.after_powers ops reserved unwrap rest D hash proof p a 10#usize g H powers
  refine ⟨pub,proof,semantic,saved,p,a,g,folded,slice,conversion,
    earlier ++ CheckpointBytes5Inputs.observe after ++ (eval H (rest (.op17 29#usize p.gamma))).1,
    (eval H (interpret impl (Port9OR_BatchCut.afterBatch D proof none p a 10#usize g inactive
      7527#usize 7751#usize 7783#usize (.Ok ())))).1,
    hpub,hproof,decoded,tx1,resumed,next,powered,batch,read,array,unwrapped,?_⟩
  have full := logs.trans (congrArg (fun tail => earlier ++ CheckpointBytes5Inputs.observe after ++ tail)
    (powerLogs.trans (congrArg (fun tail => (eval H (rest (.op17 29#usize p.gamma))).1 ++ tail) batchLogs)))
  dsimp only [impl,Port9OR_Installed.implementation] at full ⊢
  simpa only [List.append_assoc] using full

#print axioms reached
end AspisR1.Port11PROV_BatchOne
end
