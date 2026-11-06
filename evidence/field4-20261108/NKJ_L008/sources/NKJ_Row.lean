import NKJ_Scalar
import NGA_Step
set_option autoImplicit false
namespace NKJ_Row
open Aeneas Aeneas.Std Result NGA_Cell

theorem index0 {α : Type} (a : Array α 3#usize) : Array.index_usize a 0#usize=ok (at3 a 0) := NGA_Cell.index α a 0
theorem index1 {α : Type} (a : Array α 3#usize) : Array.index_usize a 1#usize=ok (at3 a 1) := NGA_Cell.index α a 1
theorem index2 {α : Type} (a : Array α 3#usize) : Array.index_usize a 2#usize=ok (at3 a 2) := NGA_Cell.index α a 2
attribute [local simp] index0 index1 index2

theorem unroll (s : Array U64 3#usize) (l r : Array U32 3#usize) :
 NKJ_Extracted.field.NKJ_reference.NKJ_row s l r = (do
 let a ← NKJ_Scalar.update (at3 s 0) (at3 l 0) (at3 r 0)
 let b ← NKJ_Scalar.update (at3 s 1) (at3 l 1) (at3 r 1)
 let c ← NKJ_Scalar.update (at3 s 2) (at3 l 2) (at3 r 2)
 ok (Array.make 3#usize [a,b,c])) := by
 simp only [NKJ_Extracted.field.NKJ_reference.NKJ_row,index0,index1,index2,bind_tc_ok,NKJ_Scalar.update]
 rfl

theorem value (s : Array U64 3#usize) (l r : Array U32 3#usize)
 (hl : ∀ i, (at3 l i).val<2147483647)
 (hr : ∀ i, (at3 r i).val<2147483647)
 (hs : ∀ i, (at3 s i).val≤3*(2147483647-1)^2) :
 ∃ out, NKJ_Extracted.field.NKJ_reference.NKJ_row s l r=ok out ∧
 ∀ i, (at3 out i).val=(at3 s i).val+(at3 l i).val*(at3 r i).val := by
 obtain ⟨a,ha,va,_⟩ := NKJ_Scalar.update_value (at3 s 0) (at3 l 0) (at3 r 0) (hl 0) (hr 0) (hs 0)
 obtain ⟨b,hb,vb,_⟩ := NKJ_Scalar.update_value (at3 s 1) (at3 l 1) (at3 r 1) (hl 1) (hr 1) (hs 1)
 obtain ⟨c,hc,vc,_⟩ := NKJ_Scalar.update_value (at3 s 2) (at3 l 2) (at3 r 2) (hl 2) (hr 2) (hs 2)
 refine ⟨Array.make 3#usize [a,b,c],?_,?_⟩
 · simp only [unroll,ha,hb,hc,bind_tc_ok]
 · intro i;fin_cases i <;> simpa [at3,Array.make] using (by first | exact va | exact vb | exact vc)
#print axioms index0
#print axioms index1
#print axioms index2
#print axioms unroll
#print axioms value
end NKJ_Row
