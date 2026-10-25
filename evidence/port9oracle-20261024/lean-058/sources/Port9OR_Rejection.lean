import Port9OR_FirstBatch
import Port7CLEAN_TraceObstruction

/-! Explicit early-rejection obstruction at the installed physical source.
These statements do not assume whole-body equality or acceptance. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_Rejection
open FS FS2 FS2.Duplex
open Aeneas Aeneas.Std Result VTop_Stages VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortStoredExperimentC4

/-- Primitive decoder rejection executes NONE of the installed op5/8/18
bodies; in particular it cannot contain an unexecuted sampler suffix. -/
theorem early (adapter : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (unwrap : Port6CK_Semantic.Unwrap) (rest : Implementation) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (i : Input) (pub proof : Slice U8)
    (hpublic : Port1_Driver.asSlice i.statement.pubBytes=some pub)
    (stored : Port1_Driver.asSlice i.stored=some proof)
    (decoder_rejected : Port1_Driver.decodeSemantic adapter pub=ok none) (H : Bytes → State) :
    eval H (Port1_Driver.rust adapter (Port9OR_Installed.implementation ops reserved unwrap rest) D hash i)=([],false) := by
  simp only [Port1_Driver.rust,hpublic,stored,decoder_rejected,eval]

/-- Unlike the historical valueOnly example, this concerns the NEW installed
physical source. It is conditional only on the primitive decoder's actual
rejected return. It is not claimed as a new deployed decoder fixture. -/
theorem no_sampler (decoder : LiteralByteProtocol.Decoder) (adapter : AdapterRw.Ops)
    (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap) (rest : Implementation)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (i : Input) (pub proof : Slice U8)
    (hpublic : Port1_Driver.asSlice i.statement.pubBytes=some pub)
    (stored : Port1_Driver.asSlice i.stored=some proof)
    (decoder_rejected : Port1_Driver.decodeSemantic adapter pub=ok none) (H : Bytes → State) :
    ¬ (∀ a, Read (eval H (RawCutProverCompiler.verifier decoder (fun _ _ => false)
      i.statement i.proof)).1 a → Read
      (eval H (Port1_Driver.rust adapter (Port9OR_Installed.implementation ops reserved unwrap rest) D hash i)).1 a) := by
  intro contains
  have frame := OraclePortReplay.frame_in_sampler decoder H i.statement i.proof 0 (by decide)
  have impossible := contains _ frame
  rw [early adapter ops reserved unwrap rest D hash i pub proof hpublic stored decoder_rejected H] at impossible
  simpa only [Read,List.map_nil,List.not_mem_nil] using impossible

#print axioms early
#print axioms no_sampler
end AspisR1.Port9OR_Rejection
end
