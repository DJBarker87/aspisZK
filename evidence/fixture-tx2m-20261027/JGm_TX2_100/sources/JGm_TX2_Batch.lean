import JGm_TX2_Terminal
import Port4B_BatchJoin
import JGc_TX2_Obstruction70
import JFn_HashBoundary
import JGk_TX2_Partial
import ARX_Root
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Batch
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge

def s0 : reference.Scratch := Port4B_BatchJoin.initial
def s1 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) := JGm_TX2_Verify0.output D hash s0
def s2 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) := JGm_TX2_Verify1.output D hash (s1 D hash)
def s3 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) := JGm_TX2_Verify2.output D hash (s2 D hash)

theorem native {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Op5T_Install.body Port4B_Install.leaves (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof JFo_Prepared.value.queries JFo_Prepared.value.roots
      JGc_TX2_Obstruction70.folded 1#usize hash=ok (.Ok () : core.result.Result Unit AspisR1Stage2.verifier.Error) := by
  have root0 : Array.index_usize JFo_Prepared.value.roots 0#usize=
      ok (encodeState JGf_TX2_M0Root.retainedRoot) := by
    change ok JFq_Root0.value=_
    exact congrArg ok (Subtype.ext JGf_TX2_M0Root.selected_root).symm
  have root1 : Array.index_usize JFo_Prepared.value.roots 1#usize=
      ok (encodeState JGh_TX2_M1Root.retainedRoot) := by
    change ok JFq_Root1.value=_
    exact congrArg ok (Subtype.ext JGh_TX2_M1Root.selected_root).symm
  have folded : JGc_TX2_Obstruction70.folded=encodeState JGc_TX2_M2Root.retainedRoot := by
    apply Subtype.ext
    rfl
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
    JGc_TX2_Obstruction70.BatchGoal (JFn_HashBoundary.dictionary JFp_SHADigest.digest D) hash := by
  change Op5T_Install.mapResult Op5T_Install.stageError
    (Op5T_Install.body Port4B_Install.leaves
      (JGc_TX2_RealLeaves.dictionary (⟨D.coremarkerCopyInst,D.digest⟩ : AspisR1Stage2.aspis_core.digest.Digest32 Hash))
      JFx_NativeBytes.proof JFo_Prepared.value.queries JFo_Prepared.value.roots
      JGc_TX2_Obstruction70.folded 1#usize hash)=_
  rw [native]
  rfl
#print axioms source
end AspisR1.JGm_TX2_Batch
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Partial
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge

/-- Actual owned-verifier facts on the SAME retained bytes and actual leaf
scratch. The native batch is included; finish/wrapper acceptance and deployment remain open. -/
def LocalFacts {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) : Prop :=
  JGk_TX2_Partial.LocalFacts ∧ ∀ s : reference.Scratch,
    reference.verify_owned (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (encodeState JGf_TX2_M0Root.retainedRoot) (JGk_TX2_Scratch0.s12 s) JGm_TX2_Supplied.nodes0=
        ok (true,JGm_TX2_Verify0.output D hash s) ∧
    reference.verify_owned (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (encodeState JGh_TX2_M1Root.retainedRoot) (JGk_TX2_Scratch1.s12 s) JGm_TX2_Supplied.nodes1=
        ok (true,JGm_TX2_Verify1.output D hash s) ∧
    reference.verify_owned (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (encodeState JGc_TX2_M2Root.retainedRoot) (JGk_TX2_Scratch2.s12 s) JGm_TX2_Supplied.nodes2=
        ok (true,JGm_TX2_Verify2.output D hash s) ∧
    Op5T_Install.body Port4B_Install.leaves (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof JFo_Prepared.value.queries JFo_Prepared.value.roots
      JGc_TX2_Obstruction70.folded 1#usize hash=ok (.Ok ())

theorem local_nonvacuity {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    LocalFacts D hash :=
  ⟨JGk_TX2_Partial.local_nonvacuity,fun s =>
    ⟨JGm_TX2_Verify0.source D hash s,JGm_TX2_Verify1.source D hash s,JGm_TX2_Verify2.source D hash s,JGm_TX2_Batch.native D hash⟩⟩
#print axioms local_nonvacuity

theorem on_saved (saved : alloc.vec.Vec U8) (same : saved.val=JFx_NativeBytes.checkpoint.val)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary JFp_SHADigest.digest D)
      (⟨saved.val,saved.property⟩ : Slice U8) JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
    LocalFacts (⟨D.coremarkerCopyInst,D.digest⟩ : AspisR1Stage2.aspis_core.digest.Digest32 Hash) hash :=
  ⟨JFn_Resume.on_saved saved same JFp_SHADigest.digest D hash realizes,local_nonvacuity _ hash⟩
#print axioms on_saved
end AspisR1.JGm_TX2_Partial
end

/- Final focused audit, attempt100: no package replay. -/
#print AspisR1.JGc_TX2_Obstruction70.BatchGoal
#print AspisR1.JFn_HashBoundary.Realizes
#print axioms AspisR1.ARX_Root.deployed
#check @AspisR1.ARX_Root.deployed
