import RPu_FJb_WideSum4
set_option autoImplicit false
namespace AspisR1.FJb_ColumnIndices
open Aeneas Aeneas.Std Result WP
theorem value (c : Usize) (hc : c.val < 4) :
    ∃ i1 i2 i3 : Usize,
      (4#usize+c : Result Usize)=ok i1 ∧ i1.val=4+c.val ∧
      (8#usize+c : Result Usize)=ok i2 ∧ i2.val=8+c.val ∧
      (12#usize+c : Result Usize)=ok i3 ∧ i3.val=12+c.val := by
  have hmax := Usize.cMax_bound_concrete.1
  have h1 : (4#usize+c : Result Usize) ⦃z=>z.val=4+c.val⦄ := by
    apply UScalar.add_spec
    scalar_tac
  have h2 : (8#usize+c : Result Usize) ⦃z=>z.val=8+c.val⦄ := by
    apply UScalar.add_spec
    scalar_tac
  have h3 : (12#usize+c : Result Usize) ⦃z=>z.val=12+c.val⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨i1,r1,v1⟩ := WP.spec_imp_exists h1
  obtain ⟨i2,r2,v2⟩ := WP.spec_imp_exists h2
  obtain ⟨i3,r3,v3⟩ := WP.spec_imp_exists h3
  exact ⟨i1,i2,i3,r1,v1,r2,v2,r3,v3⟩
#print axioms value
end AspisR1.FJb_ColumnIndices
