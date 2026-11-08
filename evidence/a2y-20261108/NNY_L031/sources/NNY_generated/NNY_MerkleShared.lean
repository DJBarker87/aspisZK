import NNY_MerkleLoop
import NNY_MerkleTreeFrame
import NKV_OkTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_MerkleShared
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NKV_StepErasure NKV_LoopTransport Port3_NativeBatchCalls

theorem treeCode (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : Bytes → AspisV8R19.SourceDuplexStep.State) (agree : NodeLeaf D H)
 (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
 (tree lo n slot : Usize) (idx outIdx : NKV_StepErasure.Indices) (val outVal : NKV_StepErasure.Values)
 (span : (lo=0#usize ∧ n=10#usize) ∨ (lo=10#usize ∧ n=12#usize))
 (treeBound : tree.val<3) (slotBound : slot.val<6)
 (canonical : ∀ j,j<22 → queries.val[j]!.val<262144)
 (run : NNY_MerkleTreeFrame.code (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
  proof queries root tree lo n slot idx val=ok (.Ok (),outIdx,outVal)) :
 NNY_MerkleTreeFrame.code Port4B_Install.leaves (VTop_Checkpoint.digest D)
  proof queries root tree lo n slot idx val=ok (.Ok (),outIdx,outVal) := by
 unfold NNY_MerkleTreeFrame.code at run ⊢
 obtain ⟨raw,keyRead,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨keys,sortRead,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 have targetKey : Port4B_Install.leaves.op4 queries lo n tree=ok raw := by
  change Port4B_KeyInstall.build queries lo n tree=ok raw
  rw [←NJS_Keys.source queries lo n tree span treeBound canonical]
  exact keyRead
 have lower : 1≤n.val := by rcases span with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
 have upper : n.val≤16 := by rcases span with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
 have targetSort : Port4B_Install.leaves.op5 raw n=ok keys := by
  change MultiproofSortRef.sort_reference.sort_rows raw 1#usize n=ok keys
  rw [←NJS_Sort.source raw n lower upper]
  exact sortRead
 obtain ⟨⟨oi,ov,pending⟩,loopRun,final⟩ := Port3_PushFrame.bind_success _ _ _ run
 cases pending with
 | none => cases final
 | some reply =>
   cases reply with
   | Err e => cases final
   | Ok u =>
     cases u
     have values := Result.ok.inj final
     have ie := congrArg (fun t => t.2.1) values
     have ve := congrArg (fun t => t.2.2) values
     dsimp only at ie ve
     subst outIdx; subst outVal
     have targetLoop := loop D H agree proof root tree lo n slot 0#usize 0#usize
      keys idx oi val ov slotBound loopRun
     rw [targetKey]
     simp only [bind_tc_ok]
     rw [targetSort]
     simp only [bind_tc_ok]
     rw [targetLoop]
     rfl

theorem slotBound (tree base : Usize) (t : tree.val<3) (b : base.val≤3) :
 (Usize.wrapping_add base tree).val<6 := by
 have cap : 6 < UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
 rw [Usize.wrapping_add_val_eq,Nat.mod_eq_of_lt (by omega)]
 omega

theorem tree (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : Bytes → AspisV8R19.SourceDuplexStep.State) (agree : NodeLeaf D H)
 (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
 (k kind : Usize) (hk : k.val<2) (tk : kind.val<3)
 (idx outIdx : NKV_StepErasure.Indices) (val outVal : NKV_StepErasure.Values)
 (canonical : ∀ j,j<22 → queries.val[j]!.val<262144)
 (run : Port3_NativeBatchBody.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H)
  (NKV_ConcreteChildren.digest H) proof queries root k kind idx val ()=ok (.Ok (),outIdx,outVal)) :
 Port3_NativeBatchBody.verifier.candidate.batch_tree (Port3_BatchStd.install Port4B_Install.leaves)
  (VTop_Checkpoint.digest D) proof queries root k kind idx val ()=ok (.Ok (),outIdx,outVal) := by
 change Port3_NativeBatchBody.verifier.candidate.batch_tree
  (Port3_BatchStd.install (NKV_ConcreteChildren.ops H)) _ _ _ _ _ _ _ _ _ = _ at run
 by_cases zero : k=0#usize
 · subst k
   rw [NNY_MerkleTreeFrame.zero] at run ⊢
   exact treeCode D H agree proof queries root kind 0#usize 10#usize _ idx outIdx val outVal
    (Or.inl ⟨rfl,rfl⟩) tk (slotBound kind 0#usize tk (by decide)) canonical run
 · have one : k=1#usize := UScalar.eq_of_val_eq (by
    have nz : k.val≠0 := by intro h;exact zero (UScalar.eq_of_val_eq h)
    change k.val=1
    omega)
   subst k
   rw [NNY_MerkleTreeFrame.one] at run ⊢
   exact treeCode D H agree proof queries root kind 10#usize 12#usize _ idx outIdx val outVal
    (Or.inr ⟨rfl,rfl⟩) tk (slotBound kind 3#usize tk (by decide)) canonical run

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
 rw [root_read roots 0,bind_tc_ok,root_read roots 1,bind_tc_ok,root_read roots 2,bind_tc_ok]
 rw [t0]
 simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
 rw [t1]
 simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
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
#print axioms treeCode
#print axioms slotBound
#print axioms tree
#print axioms values
#print axioms parent
end AspisR1.NNY_MerkleShared
end
