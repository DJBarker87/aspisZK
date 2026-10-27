import Port9OR_BatchTree

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_Batch
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
  let (r,idx1,val1) ← Port9OR_BatchTree.code base D hash proof queries root0 which 0#usize idx val
  let cf ← liftResult (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | .Continue _ =>
    let (r1,idx2,val2) ← Port9OR_BatchTree.code base D hash proof queries root1 which 1#usize idx1 val1
    let cf1 ← liftResult (core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf1 with
    | .Continue _ =>
      let (r2,_,_) ← Port9OR_BatchTree.code base D hash proof queries root2 which 2#usize idx2 val2
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

theorem values_source (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D E : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize) (roots : Array Digest 3#usize) (which : Usize) :
    erase E hash (values base D hash proof queries roots which)=
      Port3_NativeBatchBody.verifier.candidate.batch_merkle_values (Port9OR_BatchStep.ops base)
        E proof queries roots which hash := by
  simp only [values,erase_bind,erase_lift,erase_pure,Port9OR_BatchTree.source]
  unfold Port3_NativeBatchBody.verifier.candidate.batch_merkle_values
  repeat
    first
    | rfl
    | (fail_if_no_progress dsimp only)
    | (fail_if_no_progress simp only [erase_bind,erase_lift,erase_pure,Port9OR_BatchTree.source])
    | (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro value success)
    | casesm (_ × _)
    | casesm (core.ops.control_flow.ControlFlow _ _)
  all_goals rfl

theorem source (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D E : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (p : verifier.Prepared) (folded : Digest) (which : Usize) :
    erase E hash (code base D hash proof p folded which)=
      Port3_NativeBatchBody.verifier.candidate.batch_merkle (Port9OR_BatchStep.ops base)
        E proof p folded which hash := by
  simp only [code,erase_bind,erase_lift,values_source]
  rfl

#print axioms values_source
#print axioms source
end AspisR1.Port9OR_Batch
end
