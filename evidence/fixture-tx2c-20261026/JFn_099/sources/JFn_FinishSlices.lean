import JFx_NativeBytes
import Tx2I_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_FinishSlices
open Aeneas Aeneas.Std Result
open MultiproofConeSlices

def round0 : Slice U8 := sub JFx_NativeBytes.proof 7527#usize 7751#usize
def round1 : Slice U8 := sub JFx_NativeBytes.proof 7783#usize 8007#usize
def message : Slice U8 := sub JFx_NativeBytes.proof 8007#usize 10055#usize

theorem first : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.proof {start:=7527#usize,«end»:=7751#usize}=ok round0 :=
  range_total _ _ _ (by decide) (by
    have size : JFx_NativeBytes.proof.val.length=57607 := JFx_NativeBytes.proofBytes_length
    change 7751≤JFx_NativeBytes.proof.val.length
    omega)

theorem second : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.proof {start:=7783#usize,«end»:=8007#usize}=ok round1 :=
  range_total _ _ _ (by decide) (by
    have size : JFx_NativeBytes.proof.val.length=57607 := JFx_NativeBytes.proofBytes_length
    change 8007≤JFx_NativeBytes.proof.val.length
    omega)

theorem finalMessage : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.proof {start:=8007#usize,«end»:=10055#usize}=ok message :=
  range_total _ _ _ (by decide) (by
    have size : JFx_NativeBytes.proof.val.length=57607 := JFx_NativeBytes.proofBytes_length
    change 10055≤JFx_NativeBytes.proof.val.length
    omega)

#print axioms first
#print axioms second
#print axioms finalMessage
end AspisR1.JFn_FinishSlices
end
