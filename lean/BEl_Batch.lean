import BEl_BatchTree
import Port9OR_Batch
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_Batch
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 CheckpointBytes5Effect

def values (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize)
    (roots : Array Digest 3#usize) (which : Usize) : Code (core.result.Result Unit verifier.Error) := do
  let idx := Array.repeat 16#usize 0#u32
  let val := Array.repeat 16#usize (Array.repeat 32#usize 0#u8)
  let root0 ← liftResult (Array.index_usize roots 0#usize)
  let root1 ← liftResult (Array.index_usize roots 1#usize)
  let root2 ← liftResult (Array.index_usize roots 2#usize)
  let (r,idx1,val1) ← BEl_BatchTree.code base D hash proof queries root0 which 0#usize idx val
  let cf ← liftResult (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | .Continue _ =>
    let (r1,idx2,val2) ← BEl_BatchTree.code base D hash proof queries root1 which 1#usize idx1 val1
    let cf1 ← liftResult (core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf1 with
    | .Continue _ =>
      let (r2,_,_) ← BEl_BatchTree.code base D hash proof queries root2 which 2#usize idx2 val2
      let cf2 ← liftResult (core.result.Result.Insts.CoreOpsTry.branch r2)
      match cf2 with
      | .Continue _ => pure (.Ok ())
      | .Break residual => liftResult (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame verifier.Error) residual)
    | .Break residual => liftResult (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame verifier.Error) residual)
  | .Break residual => liftResult (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame verifier.Error) residual)

def code (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (proof : Slice U8)
    (p : verifier.Prepared) (folded : Digest) (which : Usize) : Code (core.result.Result Unit verifier.Error) := do
  let root0 ← liftResult (Array.index_usize p.roots 0#usize)
  let root1 ← liftResult (Array.index_usize p.roots 1#usize)
  values base D hash proof p.queries (Array.make 3#usize [root0,root1,folded]) which

/-- Three actual tree calls, sharing every live scratch return and one ordered
recorder/backend state. Every pure or digest rejection short-circuits before
the same next call; no independently chosen successful tree is assumed. -/
theorem values_observation {S Hash : Type}
    (call : SdkC_Source.Parts → S → Result SdkC_Source.Digest × S)
    (base : Port3_NativeBatchBody.Ops) (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize) (roots : Array Digest 3#usize) (which : Usize) :
    BEl_CodeCongr.Equivalent call (values base D hash proof queries roots which)
      (Port9OR_Batch.values base D hash proof queries roots which) := by
  unfold values Port9OR_Batch.values
  apply BEl_CodeCongr.bind_tail
  intro root0
  apply BEl_CodeCongr.bind_tail
  intro root1
  apply BEl_CodeCongr.bind_tail
  intro root2
  apply BEl_CodeCongr.bind_both
  · exact BEl_BatchTree.observation call base D hash proof queries root0 which _ _ _
  · intro firstReturn
    obtain ⟨r,idx1,val1⟩ := firstReturn
    apply BEl_CodeCongr.bind_tail
    intro cf
    cases cf with
    | Break residual => intro state before; rfl
    | Continue ignored =>
      apply BEl_CodeCongr.bind_both
      · exact BEl_BatchTree.observation call base D hash proof queries root1 which _ idx1 val1
      · intro secondReturn
        obtain ⟨r1,idx2,val2⟩ := secondReturn
        apply BEl_CodeCongr.bind_tail
        intro cf1
        cases cf1 with
        | Break residual => intro state before; rfl
        | Continue ignored1 =>
          apply BEl_CodeCongr.bind_head
          exact BEl_BatchTree.observation call base D hash proof queries root2 which _ idx2 val2

theorem observation {S Hash : Type}
    (call : SdkC_Source.Parts → S → Result SdkC_Source.Digest × S)
    (base : Port3_NativeBatchBody.Ops) (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (p : verifier.Prepared) (folded : Digest) (which : Usize) :
    BEl_CodeCongr.Equivalent call (code base D hash proof p folded which)
      (Port9OR_Batch.code base D hash proof p folded which) := by
  unfold code Port9OR_Batch.code
  apply BEl_CodeCongr.bind_tail
  intro root0
  apply BEl_CodeCongr.bind_tail
  intro root1
  exact values_observation call base D hash proof p.queries _ which

#print axioms values_observation
#print axioms observation
end AspisR1.BEl_Batch
end
