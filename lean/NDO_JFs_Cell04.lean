import NDO_JFu_PublicRange
set_option autoImplicit false
namespace AspisR1.JFs_Cell04
open Aeneas Aeneas.Std Result

def bytes : List U8 := [34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8,242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8,55#u8,157#u8,211#u8,124#u8,152#u8,170#u8,59#u8,88#u8,182#u8,77#u8,252#u8,152#u8,45#u8,26#u8,82#u8,63#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (JFx_NativeBytes.publicInput.val.drop 1672).take 32=bytes := by
  change (JFx_DataPublic00.bytes.drop 1672).take 32=bytes
  simp only [JFx_DataPublic00.bytes,JFx_DataPublic00.c00_length,JFx_DataPublic00.c01_length,JFx_DataPublic00.c02_length,JFx_DataPublic00.c03_length,JFx_DataPublic00.c04_length,JFx_DataPublic00.c05_length,JFx_DataPublic00.c06_length,JFx_DataPublic00.c07_length,JFx_DataPublic00.c08_length,JFx_DataPublic00.c09_length,JFx_DataPublic00.c10_length,JFx_DataPublic00.c11_length,JFx_DataPublic00.c12_length,JFx_DataPublic00.c13_length,JFx_DataPublic00.c14_length,JFx_DataPublic00.c15_length,JFx_DataPublic00.c16_length,JFx_DataPublic00.c17_length,JFx_DataPublic00.c18_length,JFx_DataPublic00.c19_length,JFx_DataPublic00.c20_length,JFx_DataPublic00.c21_length,JFx_DataPublic00.c22_length,JFx_DataPublic00.c23_length,JFx_DataPublic00.c24_length,JFx_DataPublic00.c25_length,JFx_DataPublic00.c26_length,JFx_DataPublic00.c27_length,JFx_DataPublic00.c28_length,JFx_DataPublic00.c29_length,JFx_DataPublic00.c30_length,JFx_DataPublic00.c31_length,JFx_DataPublic00.c32_length,JFx_DataPublic00.c33_length,JFx_DataPublic00.c34_length,JFx_DataPublic00.c35_length,JFx_DataPublic00.c36_length,JFx_DataPublic00.c37_length,JFx_DataPublic00.c38_length,JFx_DataPublic00.c39_length,JFx_DataPublic00.c40_length,JFx_DataPublic00.c41_length,JFx_DataPublic00.c42_length,JFx_DataPublic00.c43_length,JFx_DataPublic00.c44_length,JFx_DataPublic00.c45_length,JFx_DataPublic00.c46_length,JFx_DataPublic00.c47_length,JFx_DataPublic00.c48_length,JFx_DataPublic00.c49_length,JFx_DataPublic00.c50_length,JFx_DataPublic00.c51_length,JFx_DataPublic00.c52_length,JFx_DataPublic00.c53_length,JFx_DataPublic00.c54_length,JFx_DataPublic00.c55_length,JFx_DataPublic00.c56_length,JFx_DataPublic00.c57_length,JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.publicInput {start:=1672#usize,«end»:=1704#usize}=
    ok (JFu_PublicRange.segment 1672 32 (by decide)) :=
  by
    have call:=JFu_PublicRange.read 1672#usize 1704#usize (by decide) (by decide)
    simpa only [show (1672#usize).val=1672 from rfl,
      show (1704#usize).val=1704 from rfl,Nat.reduceSub] using call

def value : Array U8 32#usize := ⟨bytes,length⟩

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.JFs_Cell04
