import FJh_InternalWeights
set_option autoImplicit false
namespace AspisR1.FJh_InternalConstantIndices
open Aeneas Aeneas.Std Result WP
open FJh_InternalWeights (index index_value)
theorem value (i : Fin 7) : ∃ offset even odd : Usize,
    (index i-2#usize : Result Usize)=ok offset ∧
    (2#usize*offset : Result Usize)=ok even ∧ even.val=2*i.val ∧
    (even+1#usize : Result Usize)=ok odd ∧ odd.val=2*i.val+1 := by
  have hv := index_value i
  have hmax := Usize.cMax_bound_concrete.1
  have ss : (index i-2#usize : Result Usize) ⦃x=>x.val=(index i).val-2⦄ := by
    apply UScalar.sub_spec
    scalar_tac
  obtain ⟨offset,rs,vs⟩ := WP.spec_imp_exists ss
  have vo : offset.val=i.val := by omega
  have ms : (2#usize*offset : Result Usize) ⦃x=>x.val=2*offset.val⦄ := by
    apply UScalar.mul_spec
    scalar_tac
  obtain ⟨even,rm,vm⟩ := WP.spec_imp_exists ms
  have as : (even+1#usize : Result Usize) ⦃x=>x.val=even.val+1⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨odd,ra,va⟩ := WP.spec_imp_exists as
  exact ⟨offset,even,odd,rs,rm,by omega,ra,by omega⟩
#print axioms value
end AspisR1.FJh_InternalConstantIndices
