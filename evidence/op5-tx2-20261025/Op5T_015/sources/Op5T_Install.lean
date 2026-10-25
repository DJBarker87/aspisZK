import Tx2I_Accepted
import Port3_BatchStd

set_option autoImplicit false
noncomputable section
namespace AspisR1.Op5T_Install
open Aeneas Aeneas.Std Result

/-- Literal extracted batch parent, retaining the native packed-key, leaf and
multiproof children as explicit parameters. All pure std leaves are installed. -/
def body (leaves : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (proof : Slice U8) (queries : Array U32 22#usize)
    (roots : Array (Array U8 32#usize) 2#usize)
    (folded : Array U8 32#usize) (batch : Usize) (hash : Hash) := do
  let root0 ← Array.index_usize roots 0#usize
  let root1 ← Array.index_usize roots 1#usize
  Port3_NativeBatchBody.verifier.candidate.batch_merkle_values
    (Port3_BatchStd.install leaves) D proof queries
    (Array.make 3#usize [root0,root1,folded]) batch hash

def currentError : AspisR1Stage2.verifier.Error → AspisR1CurrentCaller.verifier.Error
  | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
  | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
  | .Checkpoint => .Checkpoint | .Allocation => .Allocation

def stageError : AspisR1Stage2.verifier.Error → VTop_Stages.verifier.Error
  | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
  | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
  | .Checkpoint => .Checkpoint | .Allocation => .Allocation

def mapResult {Err : Type} (map : AspisR1Stage2.verifier.Error → Err)
    (r : Result (core.result.Result Unit AspisR1Stage2.verifier.Error)) :
    Result (core.result.Result Unit Err) := do
  let value ← r
  match value with | .Ok x => ok (.Ok x) | .Err e => ok (.Err (map e))

def currentBatch (leaves : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared)
    (folded : Array U8 32#usize) (batch : Usize) (hash : Hash) :=
  mapResult currentError (body leaves {coremarkerCopyInst := D.coremarkerCopyInst, digest := D.digest} proof p.queries p.roots folded batch hash)

def stageBatch (leaves : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared)
    (folded : Array U8 32#usize) (batch : Usize) (hash : Hash) :=
  mapResult stageError (body leaves {coremarkerCopyInst := D.coremarkerCopyInst, digest := D.digest} proof p.queries p.roots folded batch hash)

/-- Only TX1's batch slot; shape is still supplied by Op3I's predecessor. -/
def current (base : AspisR1CurrentCaller.Ops) (leaves : Port3_NativeBatchBody.Ops) :
    AspisR1CurrentCaller.Ops := {base with op6 := currentBatch leaves}

/-- Only TX2's inner batch slot; authenticated TX2, shape and finish remain
installed by Tx2I_Install on this specialised stage dictionary. -/
def stage (base : VTop_Stages.Ops) (leaves : Port3_NativeBatchBody.Ops) : VTop_Stages.Ops :=
  {base with op5 := stageBatch leaves}

theorem map_success_iff {Err : Type} (map : AspisR1Stage2.verifier.Error → Err)
    (r : Result (core.result.Result Unit AspisR1Stage2.verifier.Error)) :
    mapResult map r = ok (.Ok ()) ↔ r = ok (.Ok ()) := by
  cases r with
  | fail e => simp [mapResult]
  | div => simp [mapResult]
  | ok value => cases value with
    | Err e => simp [mapResult]
    | Ok x => cases x; simp [mapResult]

theorem other_current (base : AspisR1CurrentCaller.Ops) (leaves : Port3_NativeBatchBody.Ops) :
    {current base leaves with op6 := base.op6} = base := by cases base; rfl

theorem other_stage (base : VTop_Stages.Ops) (leaves : Port3_NativeBatchBody.Ops) :
    {stage base leaves with op5 := base.op5} = base := by cases base; rfl

theorem tx1_slot (adapter : AdapterRw.Ops) (base : AspisR1CurrentCaller.Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (leaves : Port3_NativeBatchBody.Ops) :
    @AspisR1CurrentCaller.Ops.op6 (RowShape_InstalledSlots.verifierOps (Op3I_Install.install (current base leaves)) B std) =
      @currentBatch leaves := rfl

theorem tx2_slot {F : Type} (base : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (leaves : Port3_NativeBatchBody.Ops) :
    @VTop_Stages.Ops.op5 (Tx2I_Install.stage (stage base leaves) finish) = @stageBatch leaves := rfl

#print axioms map_success_iff
#print axioms other_current
#print axioms other_stage
#print axioms tx1_slot
#print axioms tx2_slot
end AspisR1.Op5T_Install
end
