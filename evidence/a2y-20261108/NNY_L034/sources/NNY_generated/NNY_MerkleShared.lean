import NNY_MerkleTrees
import NKV_OkTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_MerkleShared
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NKV_StepErasure NKV_LoopTransport Port3_NativeBatchCalls

theorem values (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : Bytes → AspisV8R19.SourceDuplexStep.State) (agree : NodeLeaf D H)
 (proof : Slice U8) (queries : Array U32 22#usize) (roots : Array (Array U8 32#usize) 3#usize)
 (k : Usize) (hk : k.val<2) (canonical : ∀ j,j<22 → queries.val[j]!.val<262144)
 (run : Port3_NativeBatchBody.verifier.candidate.batch_merkle_values (NKV_ConcreteChildren.ops H)
  (NKV_ConcreteChildren.digest H) proof queries roots k ()=ok (.Ok ())) :
 Port3_NativeBatchBody.verifier.candidate.batch_merkle_values (Port3_BatchStd.install Port4B_Install.leaves)
  (VTop_Checkpoint.digest D) proof queries roots k ()=ok (.Ok ()) := by
 obtain ⟨i1,i2,i3,v1,v2,v3,c0,c1,c2⟩ := values_calls _ _ () proof queries roots k run
 have t0 := tree D H agree proof queries (rootAt roots 0) k 0#usize hk (by decide) _ i1 _ v1 canonical c0
 have t1 := tree D H agree proof queries (rootAt roots 1) k 1#usize hk (by decide) i1 i2 v1 v2 canonical c1
 have t2 := tree D H agree proof queries (rootAt roots 2) k 2#usize hk (by decide) i2 i3 v2 v3 canonical c2
 unfold Port3_NativeBatchBody.verifier.candidate.batch_merkle_values
 have h0 : Array.index_usize roots 0#usize=ok (Port3_NativeBatchCalls.rootAt roots 0) := Port3_NativeBatchCalls.root_read roots 0
 have h1 : Array.index_usize roots 1#usize=ok (Port3_NativeBatchCalls.rootAt roots 1) := Port3_NativeBatchCalls.root_read roots 1
 have h2 : Array.index_usize roots 2#usize=ok (Port3_NativeBatchCalls.rootAt roots 2) := Port3_NativeBatchCalls.root_read roots 2
 rw [h0,bind_tc_ok,h1,bind_tc_ok,h2,bind_tc_ok]
 rw [t0]
 dsimp only [Aeneas.Std.uncurry,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
 rw [t1]
 dsimp only [Aeneas.Std.uncurry,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
 rw [t2]
 rfl

/-- Lane-neutral parent. Agreement is discharged per lane; it is never an A1/A2 premise. -/
theorem parent (H : Bytes → AspisV8R19.SourceDuplexStep.State)
 (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (agree : NodeLeaf D H)
 (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (folded : Array U8 32#usize)
 (k : Usize) (hk : k.val<2) (q : ∀ j,j<22 → p.queries.val[j]!.val<262144)
 (accepted : NHT_ResultPort.action (NKV_FRef.verifier.candidate.batch_merkle
  (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H) proof p folded k ())=ok (.Ok ())) :
 Port4B_Install.batch D proof p folded k ()=ok (.Ok ()) := by
 have native := (NKV_OkTransport.batch H proof p folded k hk).mpr (NHT_ResultSuccess.source _ () accepted)
 unfold Port3_NativeBatchBody.verifier.candidate.batch_merkle at native
 obtain ⟨r0,read0,native⟩ := Port3_PushFrame.bind_success _ _ _ native
 obtain ⟨r1,read1,native⟩ := Port3_PushFrame.bind_success _ _ _ native
 have result := values D H agree proof p.queries (Array.make 3#usize [r0,r1,folded]) k hk q native
 unfold Port4B_Install.batch Port3_BatchStage.batch
 apply (Port3_QueryInstall.success_iff _ _).mpr
 unfold Port3_NativeBatchBody.verifier.candidate.batch_merkle
 rw [read0,bind_tc_ok,read1,bind_tc_ok]
 exact result
#print axioms values
#print axioms parent
end AspisR1.NNY_MerkleShared
end
