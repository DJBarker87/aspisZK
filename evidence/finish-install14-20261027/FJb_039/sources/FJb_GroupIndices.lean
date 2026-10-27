import FJb_MatrixGroupStep
set_option autoImplicit false
namespace AspisR1.FJb_GroupIndices
open Aeneas Aeneas.Std Result WP
/-- Checked source arithmetic for four lanes and the next group. -/
theorem value (g : Usize) (hg : g.val < 4) :
    ∃ i0 i1 i2 i3 next : Usize,
      (4#usize*g : Result Usize)=ok i0 ∧ i0.val=4*g.val ∧
      (i0+1#usize : Result Usize)=ok i1 ∧ i1.val=4*g.val+1 ∧
      (i0+2#usize : Result Usize)=ok i2 ∧ i2.val=4*g.val+2 ∧
      (i0+3#usize : Result Usize)=ok i3 ∧ i3.val=4*g.val+3 ∧
      (g+1#usize : Result Usize)=ok next ∧ next.val=g.val+1 := by
  have hmax := Usize.cMax_bound_concrete.1
  have hm : (4#usize*g : Result Usize) ⦃z=>z.val=4*g.val⦄ := by
    apply UScalar.mul_spec
    scalar_tac
  obtain ⟨i0,h0,v0⟩ := WP.spec_imp_exists hm
  have h1 : (i0+1#usize : Result Usize) ⦃z=>z.val=i0.val+1⦄ := by
    apply UScalar.add_spec
    scalar_tac
  have h2 : (i0+2#usize : Result Usize) ⦃z=>z.val=i0.val+2⦄ := by
    apply UScalar.add_spec
    scalar_tac
  have h3 : (i0+3#usize : Result Usize) ⦃z=>z.val=i0.val+3⦄ := by
    apply UScalar.add_spec
    scalar_tac
  have hn : (g+1#usize : Result Usize) ⦃z=>z.val=g.val+1⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨i1,r1,v1⟩ := WP.spec_imp_exists h1
  obtain ⟨i2,r2,v2⟩ := WP.spec_imp_exists h2
  obtain ⟨i3,r3,v3⟩ := WP.spec_imp_exists h3
  obtain ⟨next,rn,vn⟩ := WP.spec_imp_exists hn
  exact ⟨i0,i1,i2,i3,next,h0,v0,r1,by omega,r2,by omega,r3,by omega,rn,vn⟩
#print axioms value
end AspisR1.FJb_GroupIndices
