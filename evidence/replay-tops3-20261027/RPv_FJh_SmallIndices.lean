import RPv_FJh_Base
set_option autoImplicit false
namespace AspisR1.FJh_SmallIndices
open Aeneas Aeneas.Std Result WP
theorem value (offset : Usize) (ho : offset.val<7) : ∃ even odd : Usize,
    (2#usize*offset : Result Usize)=ok even ∧ even.val=2*offset.val ∧
    (even+1#usize : Result Usize)=ok odd ∧ odd.val=2*offset.val+1 := by
  have hmax := Usize.cMax_bound_concrete.1
  have ms : (2#usize*offset : Result Usize) ⦃x=>x.val=2*offset.val⦄ := by
    apply UScalar.mul_spec
    scalar_tac
  obtain ⟨even,rm,vm⟩ := WP.spec_imp_exists ms
  have adds : (even+1#usize : Result Usize) ⦃x=>x.val=even.val+1⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨odd,ra,va⟩ := WP.spec_imp_exists adds
  exact ⟨even,odd,rm,vm,ra,by omega⟩
#print axioms value
end AspisR1.FJh_SmallIndices
