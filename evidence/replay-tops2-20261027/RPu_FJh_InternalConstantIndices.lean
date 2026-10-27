import RPu_FJh_InternalWeights
import RPu_FJh_SmallIndices
set_option autoImplicit false
namespace AspisR1.FJh_InternalConstantIndices
open Aeneas Aeneas.Std Result WP
open FJh_InternalWeights (index index_value)
theorem value (i : Fin 7) : ∃ offset even odd : Usize,
    (index i-2#usize : Result Usize)=ok offset ∧
    (2#usize*offset : Result Usize)=ok even ∧ even.val=2*i.val ∧
    (even+1#usize : Result Usize)=ok odd ∧ odd.val=2*i.val+1 := by
  have h2 : (2#usize).val=2 := by scalar_tac
  have h1 : (1#usize).val=1 := by scalar_tac
  have hv := index_value i
  have hmax := Usize.cMax_bound_concrete.1
  have ss := UScalar.sub_spec (x:=index i) (y:=2#usize)
    (by change 2≤(index i).val;omega)
  obtain ⟨offset,rs,vs,hlo⟩ := WP.spec_imp_exists ss
  rw [h2] at vs
  have vo : offset.val=i.val := by omega
  obtain ⟨even,odd,rm,vm,ra,va⟩ := FJh_SmallIndices.value offset (by omega)
  exact ⟨offset,even,odd,rs,rm,by omega,ra,by omega⟩
#print axioms value
end AspisR1.FJh_InternalConstantIndices
