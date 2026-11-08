import NNY_MerkleLoop
import NNY_MerkleTreeFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_MerkleShared
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NKV_StepErasure NKV_LoopTransport

theorem treeCode (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : Bytes → AspisV8R19.SourceDuplexStep.State) (agree : NodeLeaf D H)
 (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
 (tree lo n slot : Usize) (idx outIdx : Indices) (val outVal : Values)
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
#print axioms treeCode
end AspisR1.NNY_MerkleShared
end
