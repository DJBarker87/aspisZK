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

#print axioms treeCode
#print axioms slotBound
#print axioms tree
end AspisR1.NNY_MerkleShared
end
