import NDH_Reference.Funs
import ExtractedMaskCoefficientArray
set_option autoImplicit false
namespace NDH_Qwrite
open Aeneas Aeneas.Std Result
open AspisR1.ExtractedMaskCoefficientArray

theorem reference (rank : Array U32 8#usize) (q : U32) (r : U64)
    (j : Usize) (positive : 0 < j.val) (bound : j.val ≤ 8) :
    ∃ index : Usize,
      index.val = j.val-1 ∧
      NDH_Reference.qwrite_ref rank q r j = ok (rank.set index q,r,index) := by
  have hp : (1#usize : Usize).val ≤ j.val := by change 1≤j.val; omega
  obtain ⟨index,sub,indexValue,_⟩ := WP.spec_imp_exists (UScalar.sub_spec (x:=j) (y:=1#usize) hp)
  change index.val=j.val-1 at indexValue
  have small : index.val < (8#usize : Usize).val := by
    change index.val < 8
    omega
  have smallLen : index.val < rank.length := by
    change index.val < rank.val.length
    rw [rank.property]
    exact small
  have hu := update_refines_set rank index q smallLen
  obtain ⟨out,update,equal⟩ := WP.spec_imp_exists hu
  rw [equal] at update
  refine ⟨index,indexValue,?_⟩
  simp only [NDH_Reference.qwrite_ref,sub,update,bind_tc_ok]

#print axioms reference
end NDH_Qwrite
