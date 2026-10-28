import NDO_JGm_TX2_Terminal
import Port4B_BatchJoin
import NDO_JGe_View
import RPz7_Op5T_Concrete
import NDO_JFn_HashBoundary
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_Batch
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window

def s0 : reference.Scratch := Port4B_BatchJoin.initial
def s1 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) := JGm_TX2_Verify0.output D hash s0
def s2 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) := JGm_TX2_Verify1.output D hash (s1 D hash)
def s3 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) := JGm_TX2_Verify2.output D hash (s2 D hash)

theorem native {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Op5T_Install.body Port4B_Install.leaves (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof JFo_Prepared.value.queries JFo_Prepared.value.roots
      JGe_View.folded 1#usize hash=ok (.Ok () : core.result.Result Unit AspisR1Stage2.verifier.Error) := by
  have root0 : Array.index_usize JFo_Prepared.value.roots 0#usize=
      ok (encodeState JGf_TX2_M0Root.retainedRoot) := by
    change ok JFq_Root0.value=_
    exact congrArg ok (Subtype.ext JGf_TX2_M0Root.selected_root).symm
  have root1 : Array.index_usize JFo_Prepared.value.roots 1#usize=
      ok (encodeState JGh_TX2_M1Root.retainedRoot) := by
    change ok JFq_Root1.value=_
    exact congrArg ok (Subtype.ext JGh_TX2_M1Root.selected_root).symm
  have folded : JGe_View.folded=encodeState JGc_TX2_M2Root.retainedRoot := by
    apply Subtype.ext
    change (JFw_Frames.window 7751 32).val=(encodeState JGc_TX2_M2Root.retainedRoot).val
    rw [JGc_TX2_M2Root.encoded_root]
    unfold JFw_Frames.window
    exact JGc_TX2_M2Root.selected_root
  rw [Op5T_Install.body,root0,bind_tc_ok,root1,bind_tc_ok,folded]
  rw [Port3_NativeBatchBody.verifier.candidate.batch_merkle_values]
  have r0 : Array.index_usize (Array.make 3#usize
      [encodeState JGf_TX2_M0Root.retainedRoot,encodeState JGh_TX2_M1Root.retainedRoot,
        encodeState JGc_TX2_M2Root.retainedRoot]) 0#usize=ok (encodeState JGf_TX2_M0Root.retainedRoot) := rfl
  have r1 : Array.index_usize (Array.make 3#usize
      [encodeState JGf_TX2_M0Root.retainedRoot,encodeState JGh_TX2_M1Root.retainedRoot,
        encodeState JGc_TX2_M2Root.retainedRoot]) 1#usize=ok (encodeState JGh_TX2_M1Root.retainedRoot) := rfl
  have r2 : Array.index_usize (Array.make 3#usize
      [encodeState JGf_TX2_M0Root.retainedRoot,encodeState JGh_TX2_M1Root.retainedRoot,
        encodeState JGc_TX2_M2Root.retainedRoot]) 2#usize=ok (encodeState JGc_TX2_M2Root.retainedRoot) := rfl
  rw [r0,bind_tc_ok,r1,bind_tc_ok,r2,bind_tc_ok]
  have t0 : Port3_NativeBatchBody.verifier.candidate.batch_tree
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof JFo_Prepared.value.queries (encodeState JGf_TX2_M0Root.retainedRoot)
      1#usize 0#usize (Array.repeat 16#usize 0#u32) (Array.repeat 16#usize (Array.repeat 32#usize 0#u8)) hash=
        ok (.Ok (), (s1 D hash).idx,(s1 D hash).val) := JGm_TX2_Terminal0.tree D hash s0
  have t1 : Port3_NativeBatchBody.verifier.candidate.batch_tree
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof JFo_Prepared.value.queries (encodeState JGh_TX2_M1Root.retainedRoot)
      1#usize 1#usize (s1 D hash).idx (s1 D hash).val hash=
        ok (.Ok (), (s2 D hash).idx,(s2 D hash).val) := JGm_TX2_Terminal1.tree D hash (s1 D hash)
  have t2 : Port3_NativeBatchBody.verifier.candidate.batch_tree
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof JFo_Prepared.value.queries (encodeState JGc_TX2_M2Root.retainedRoot)
      1#usize 2#usize (s2 D hash).idx (s2 D hash).val hash=
        ok (.Ok (), (s3 D hash).idx,(s3 D hash).val) := JGm_TX2_Terminal2.tree D hash (s2 D hash)
  rw [t0]
  change (do
    let (r1,idx2,val2) ← Port3_NativeBatchBody.verifier.candidate.batch_tree
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof JFo_Prepared.value.queries (encodeState JGh_TX2_M1Root.retainedRoot)
      1#usize 1#usize (s1 D hash).idx (s1 D hash).val hash
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | .Continue _ => do
      let (r2,_,_) ← Port3_NativeBatchBody.verifier.candidate.batch_tree
        (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
        JFx_NativeBytes.proof JFo_Prepared.value.queries (encodeState JGc_TX2_M2Root.retainedRoot)
        1#usize 2#usize idx2 val2 hash
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | .Continue _ => ok (.Ok () : core.result.Result Unit AspisR1Stage2.verifier.Error)
      | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame AspisR1Stage2.verifier.Error) residual
    | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame AspisR1Stage2.verifier.Error) residual)=ok (.Ok () : core.result.Result Unit AspisR1Stage2.verifier.Error)
  rw [t1]
  change (do
    let (r2,_,_) ← Port3_NativeBatchBody.verifier.candidate.batch_tree
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof JFo_Prepared.value.queries (encodeState JGc_TX2_M2Root.retainedRoot)
      1#usize 2#usize (s2 D hash).idx (s2 D hash).val hash
    let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf2 with
    | .Continue _ => ok (.Ok () : core.result.Result Unit AspisR1Stage2.verifier.Error)
    | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame AspisR1Stage2.verifier.Error) residual)=ok (.Ok () : core.result.Result Unit AspisR1Stage2.verifier.Error)
  rw [t2]
  rfl
#print axioms native

theorem source {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Op5T_Install.stageBatch Port4B_Install.leaves (JFn_HashBoundary.dictionary JFp_SHADigest.digest D)
      JFx_NativeBytes.proof JFo_Prepared.value JGe_View.folded 1#usize hash=ok (.Ok ()) := by
  change Op5T_Install.mapResult Op5T_Install.stageError
    (Op5T_Install.body Port4B_Install.leaves
      (JGc_TX2_RealLeaves.dictionary (⟨D.coremarkerCopyInst,D.digest⟩ : AspisR1Stage2.aspis_core.digest.Digest32 Hash))
      JFx_NativeBytes.proof JFo_Prepared.value.queries JFo_Prepared.value.roots
      JGe_View.folded 1#usize hash)=_
  rw [native]
  rfl
#print axioms source
end AspisR1.JGx_Batch
end
