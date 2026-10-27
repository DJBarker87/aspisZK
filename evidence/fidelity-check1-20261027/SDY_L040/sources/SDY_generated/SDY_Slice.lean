import SDY_Loop
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace SDY_Slice

def nodes (x : U8) : Slice U8 := ⟨List.replicate 224 x,by simp only [List.length_replicate]; scalar_tac⟩
def sibling (x : U8) : Slice U8 := ⟨List.replicate 32 x,by simp only [List.length_replicate]; scalar_tac⟩

#print List.slice
#print core.slice.Slice.copy_from_slice

theorem read (x : U8) (a b : Usize) (lo : a.val ≤ b.val) (hi : b.val ≤ 224)
    (width : b.val - a.val = 32) :
    core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8) (nodes x) {start:=a,«end»:=b} = ok (some (sibling x)) := by
  unfold core.slice.Slice.get core.slice.index.SliceIndexRangeUsizeSlice core.slice.index.SliceIndexRangeUsizeSlice.get
  simp only [nodes,Slice.length,List.length_replicate]
  have cond : a ≤ b ∧ b.val ≤ 224 := by constructor; exact lo; exact hi
  simp only [cond,↓reduceIte]
  congr 2
  apply Subtype.eq
  simp [List.slice,List.drop_replicate,List.take_replicate,sibling,width]
  omega
#print axioms read
end SDY_Slice
