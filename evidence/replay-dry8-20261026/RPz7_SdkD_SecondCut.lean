import RPz7_SdkD_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_SecondCut
open Aeneas Aeneas.Std Result VTop_Stages

/-- Reader and copied folded root are retained from the SAME TX2 prefix. -/
theorem common (ops : Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8)
    (start : ops.op15 = ok 7751#usize) (finish : ops.op14 = ok 7783#usize)
    (unwrap : ops.unwrap32 = Port4B_FoldedCut.unwrap32)
    (success : verifier.candidate.tx2_common ops D pub proof checkpoint hash none = ok (.Ok ())) :
    ∃ (p : verifier.Prepared) (a : verifier.Accumulator) (root : Array U8 32#usize) (view : Slice U8),
      ops.op18 D checkpoint proof pub .S2 hash = ok (.Ok (p,a)) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=7751#usize,«end»:=7783#usize} = ok view ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view = ok (.Ok root) ∧
      ops.op5 D proof p root 1#usize hash = ok (.Ok ()) := by
  rw [←Tx2I_Cuts.common_source] at success
  unfold Tx2I_Cuts.common at success
  rw [start,finish,unwrap] at success
  repeat' first
  | (solve | cases success)
  | uncase_result
  | head_reduce success
  | split at success
  all_goals exact ⟨_,_,_,_,by assumption,by assumption,by assumption,by assumption⟩

#print axioms common
end AspisR1.SdkD_SecondCut
end
