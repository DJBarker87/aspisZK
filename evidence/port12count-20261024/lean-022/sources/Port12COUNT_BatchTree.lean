import Port12COUNT_BatchLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port12COUNT_BatchTree
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values)
open Port12COUNT_Verify Port12COUNT_BatchLeaf Port12COUNT_BatchTail
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem count (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (proof : Slice U8) (queries : Array U32 22#usize) (root : Digest)
    (batch tree : Usize) (idx : Indices) (val : Values) (cap : Usize)
    (capRead : Array.index_usize capacities (Port4B_TreeCuts.slot batch tree)=ok cap)
    (small : cap.val≤172) (nonzero : 0<cap.val) :
    (eval H (Port9OR_Code.program D hash
      (Port9OR_BatchTree.code base D hash proof queries root batch tree idx val))).1.length≤
      cap.val+2*(if batch=0#usize then 10 else 12)-1 := by
  unfold Port9OR_BatchTree.code
  simp only [Port9OR_BatchStep.pair_match]
  apply lift_cap; intro raw
  apply lift_cap; intro keys
  have nSmall : (Port4B_TreeCuts.count batch).val<256 := by
    rw [(Port4B_Bounds.count batch).1];split <;> decide
  have first := Port12COUNT_BatchLoop.count base D hash H proof root tree (Port4B_TreeCuts.lo batch)
    (Port4B_TreeCuts.count batch) (Port4B_TreeCuts.slot batch tree) keys
    ((Port4B_TreeCuts.count batch).val+1) idx val 0#usize 0#usize cap capRead small nonzero nSmall
  have joined := bind_count D hash H (Port9OR_BatchLoop.code base D hash proof root tree (Port4B_TreeCuts.lo batch)
    (Port4B_TreeCuts.count batch) (Port4B_TreeCuts.slot batch tree) keys
    ((Port4B_TreeCuts.count batch).val+1) idx val 0#usize 0#usize)
    (fun out => match out.2.2 with
      | none => liftResult (fail .panic)
      | some r => pure (r,out.1,out.2.1))
    (cap.val+2*(Port4B_TreeCuts.count batch).val-1) 0 (by simpa using first) (by
      intro out _
      obtain ⟨outIdx,outVal,pending⟩ := out
      cases pending <;> exact Nat.zero_le 0)
  simpa only [(Port4B_Bounds.count batch).1,Nat.add_zero] using joined

/-- Tiny table/source-header calculations, no physical height unfolding. -/
theorem batch0 (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (proof : Slice U8) (queries : Array U32 22#usize) (root : Digest)
    (tree : Usize) (idx : Indices) (val : Values) (kind : tree.val<3) :
    (eval H (Port9OR_Code.program D hash
      (Port9OR_BatchTree.code base D hash proof queries root 0#usize tree idx val))).1.length≤
      if tree=2#usize then 147 else 165 := by
  have cases : tree=0#usize ∨ tree=1#usize ∨ tree=2#usize := by scalar_tac
  rcases cases with rfl | rfl | rfl
  all_goals
    first
    | (exact (by simpa using count base D hash H proof queries root 0#usize 0#usize idx val 146#usize (by simp [capacities,Array.index_usize,Array.getElem?_Usize_eq,Port4B_Bounds.slot _ _ (by decide) (by decide)]) (by decide) (by decide)))
    | (exact (by simpa using count base D hash H proof queries root 0#usize 1#usize idx val 146#usize (by simp [capacities,Array.index_usize,Array.getElem?_Usize_eq,Port4B_Bounds.slot _ _ (by decide) (by decide)]) (by decide) (by decide)))
    | (exact (by simpa using count base D hash H proof queries root 0#usize 2#usize idx val 128#usize (by simp [capacities,Array.index_usize,Array.getElem?_Usize_eq,Port4B_Bounds.slot _ _ (by decide) (by decide)]) (by decide) (by decide)))

theorem batch1 (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (proof : Slice U8) (queries : Array U32 22#usize) (root : Digest)
    (tree : Usize) (idx : Indices) (val : Values) (kind : tree.val<3) :
    (eval H (Port9OR_Code.program D hash
      (Port9OR_BatchTree.code base D hash proof queries root 1#usize tree idx val))).1.length≤
      if tree=2#usize then 173 else 195 := by
  have cases : tree=0#usize ∨ tree=1#usize ∨ tree=2#usize := by scalar_tac
  rcases cases with rfl | rfl | rfl
  all_goals
    first
    | (exact (by simpa using count base D hash H proof queries root 1#usize 0#usize idx val 172#usize (by simp [capacities,Array.index_usize,Array.getElem?_Usize_eq,Port4B_Bounds.slot _ _ (by decide) (by decide)]) (by decide) (by decide)))
    | (exact (by simpa using count base D hash H proof queries root 1#usize 1#usize idx val 172#usize (by simp [capacities,Array.index_usize,Array.getElem?_Usize_eq,Port4B_Bounds.slot _ _ (by decide) (by decide)]) (by decide) (by decide)))
    | (exact (by simpa using count base D hash H proof queries root 1#usize 2#usize idx val 150#usize (by simp [capacities,Array.index_usize,Array.getElem?_Usize_eq,Port4B_Bounds.slot _ _ (by decide) (by decide)]) (by decide) (by decide)))

#print axioms count
#print axioms batch0
#print axioms batch1
end AspisR1.Port12COUNT_BatchTree
end
