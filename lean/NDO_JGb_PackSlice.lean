import NDO_FIw_PackTotal
import RPv_JFy_PreparedSteps
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGb_PackSlice
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)

@[step] theorem pack (s : Slice field.QM31) (len : s.length=4)
    (hc : ∀ x∈s.val,Canon x) : field.qm31_pack_base4 s ⦃ out => Canon out ⦄ := by
  obtain ⟨out,call,hc1⟩ := FIw_PackTotal.source s len hc
  rw [call]
  exact hc1
#print axioms pack

theorem source (a : Array field.QM31 16#usize) (lo hi : Usize)
    (hlen : lo.val+4=hi.val) (hhi : hi.val≤16) (hc : canonical a) :
    ∃ s,core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice field.QM31)) a ⟨lo,hi⟩=ok s ∧
      s.length=4 ∧ (∀ x∈s.val,Canon x) := by
  have spec : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice field.QM31)) a ⟨lo,hi⟩
      ⦃ s => s.val=List.slice lo.val hi.val a.val ⦄ := by
    step* <;> first | scalar_tac | assumption
  obtain ⟨s,call,same⟩ := WP.spec_imp_exists spec
  refine ⟨s,call,?_,?_⟩
  · change s.val.length=4
    rw [same]
    simp only [List.slice,List.length_take,List.length_drop,a.property]
    change min (hi.val-lo.val) (16-lo.val)=4
    omega
  · intro x hx
    rw [same] at hx
    exact hc x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
#print axioms source
end AspisR1.JGb_PackSlice
end
