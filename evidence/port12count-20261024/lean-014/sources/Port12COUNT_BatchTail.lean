import Port12COUNT_BatchLeaf
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port12COUNT_BatchTail
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values Next Out)
open Port12COUNT_Verify Port12COUNT_BatchLeaf
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def capacities : Array Usize 6#usize :=
  Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize]

theorem prefix_length (nodes supplied : Slice U8) (stop : Usize)
    (read : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      nodes {«end»:=stop}=ok supplied) : supplied.val.length≤stop.val := by
  simp only [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeToUsizeSlice.index] at read
  split at read
  · cases Result.ok.inj read
    simp only [List.length_take]
    exact Nat.min_le_left _ _
  · cases read

theorem verify {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (root : Digest) (idx : Indices) (val : Values) (d : Usize) (nodes : Slice U8) :
    (eval H (Port9OR_Code.program D hash (Port9OR_BatchStep.verify root idx val d nodes))).1.length≤
      nodes.val.length/32+d.val-1 := by
  unfold Port9OR_BatchStep.verify
  have bound := bind_count D hash H _ _ (nodes.val.length/32+d.val-1) 0
    (Port12COUNT_Verify.count D hash H root ⟨idx,val,d,0#usize⟩ nodes) (by
      intro out _
      obtain ⟨b,s⟩ := out
      change 0≤0
      omega)
  simpa using bound

/-- Physical terminal path: actual capacity guard, padding scan and used slice,
including every rejected/partial/outer failure path before or after P6. -/
theorem terminal (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (proof : Slice U8) (root : Digest) (tree lo n slot : Usize) (keys : Array U64 16#usize)
    (idx : Indices) (val : Values) (d pos cap : Usize) (stopped : ¬pos<n)
    (capRead : Array.index_usize capacities slot=ok cap) (small : cap.val≤172) :
    (eval H (Port9OR_Code.program D hash
      (Port9OR_BatchStep.body base D proof root tree hash lo n slot keys idx val d pos))).1.length≤cap.val+d.val-1 := by
  dsimp only [capacities] at capRead
  unfold Port9OR_BatchStep.body
  rw [if_neg stopped]
  simp only [Port9OR_BatchStep.ops,Port3_BatchStd.install,eval_lift_join,capRead,lift]
  repeat' first
  | (solve | exact Nat.zero_le _)
  | (fail_if_no_progress simp only [eval_lift_join])
  | split
  | casesm (_ × _)
  | casesm (core.ops.control_flow.ControlFlow _ _)
  all_goals
    match goal with
    | hprefix : core.slice.index.Slice.index _ _ {«end»:=Usize.wrapping_mul 32#usize ?used}=ok ?supplied,
      fit : ¬ ?used > cap |- _ =>
      have width := prefix_length _ supplied (Usize.wrapping_mul 32#usize used) hprefix
      have usedSmall : used.val≤288 := by change ¬used.val>cap.val at fit;omega
      rw [Port4B_SliceReads.scaled used usedSmall] at width
      have first := (verify D hash H root idx val d supplied).trans
        (show supplied.val.length/32+d.val-1≤cap.val+d.val-1 by
          change ¬used.val>cap.val at fit;omega)
      have joined := bind_count D hash H _ _ (cap.val+d.val-1) 0 first (by
        intro out _
        obtain ⟨b,idx',val'⟩ := out
        split <;> exact Nat.zero_le 0)
      simpa using joined

#print axioms prefix_length
#print axioms verify
#print axioms terminal
end AspisR1.Port12COUNT_BatchTail
end
