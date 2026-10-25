import Port6AUTH_Frames
import Port1_StoredCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port7CLEAN_TraceObstruction
open FS FS2 FS2.Duplex
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortStoredExperimentC4

/-- A concrete value-correct interpretation of ANY source dictionary. It
performs no oracle effects. Thus pure native return laws do not pin the trace. -/
def valueOnly (ops : Ops) : Implementation := fun call => .done (invoke ops call)

theorem interpret_empty (ops : Ops) {A : Type} (tree : Code A) (H : Bytes → State) :
    (eval H (interpret (valueOnly ops) tree)).1=[] := by
  induction tree with
  | done a => rfl
  | step r k ih =>
    cases r with
    | fail e => rfl
    | div => rfl
    | ok x => exact ih x
  | call op k ih =>
    simp only [interpret,valueOnly,eval_bind,eval,List.nil_append]
    cases h : invoke ops op with
    | fail e => rfl
    | div => rfl
    | ok x => exact ih x

theorem stages_empty (ops : Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (H : Bytes → State) :
    (eval H (Port1_Driver.stages (valueOnly ops) D hash semantic pub proof)).1=[] := by
  unfold Port1_Driver.stages
  simp only [eval_bind,interpret_empty,List.nil_append]
  cases h : (eval H (interpret (valueOnly ops)
    (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))).2 with
  | fail e => rfl
  | div => rfl
  | ok result =>
    cases result with
    | Err e => rfl
    | Ok saved => simp only [eval_bind,interpret_empty,eval,List.nil_append,List.append_nil]

theorem driver_empty (adapter : AdapterRw.Ops) (ops : Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (i : Input) (H : Bytes → State) :
    (eval H (Port1_Driver.rust adapter (valueOnly ops) D hash i)).1=[] := by
  unfold Port1_Driver.rust
  split
  · split
    · exact stages_empty ops D hash _ _ _ H
    · rfl
  · rfl

/-- Exact obstruction to universally instantiating the source sampler
embedding from the driver type/native values alone. This is NOT a
counterexample to a pinned effectful frozen driver. -/
theorem no_sampler_embedding (decoder : LiteralByteProtocol.Decoder)
    (adapter : AdapterRw.Ops) (ops : Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (i : Input) (H : Bytes → State) :
    ¬ (∀ a, Read (eval H (RawCutProverCompiler.verifier decoder (fun _ _ => false)
      i.statement i.proof)).1 a →
      Read (eval H (Port1_Driver.rust adapter (valueOnly ops) D hash i)).1 a) := by
  intro contains
  have frame := OraclePortReplay.frame_in_sampler decoder H i.statement i.proof 0 (by decide)
  have impossible := contains _ frame
  rw [driver_empty] at impossible
  exact impossible

#print axioms interpret_empty
#print axioms stages_empty
#print axioms driver_empty
#print axioms no_sampler_embedding
end AspisR1.Port7CLEAN_TraceObstruction
end
