import JGo_TX2_Root
import AuS1_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_OuterRoot
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window

def get (base : VTop_Stages.Ops) : Result (Array U8 32#usize) := do
  let start ← (AuS1_Install.base base).op15
  let stop ← (AuS1_Install.base base).op14
  let bytes ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.proof {start:=start,«end»:=stop}
  let array ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 bytes
  (AuS1_Install.base base).unwrap32 array

theorem source (base : VTop_Stages.Ops) : get base=ok JGc_TX2_Obstruction70.folded := by
  change (do
    let bytes ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      JFx_NativeBytes.proof {start:=7751#usize,«end»:=7783#usize}
    let array ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 bytes
    Port4B_FoldedCut.unwrap32 array)=_
  rw [JGo_TX2_Root.read,bind_tc_ok,JGo_TX2_Root.array,bind_tc_ok]
  rfl
#print axioms source

theorem batch (base : VTop_Stages.Ops) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    (do
      let root ← get base
      (Op5T_Concrete.stage (AuS1_Install.base base)).op5
        (JFn_HashBoundary.dictionary JFp_SHADigest.digest D)
        JFx_NativeBytes.proof JFo_Prepared.value root 1#usize hash)=ok (.Ok ()) := by
  rw [source,bind_tc_ok]
  exact JGm_TX2_Batch.source D hash
#print axioms batch
end AspisR1.JGo_TX2_OuterRoot
end
