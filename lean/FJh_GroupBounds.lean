import FJh_Base
set_option autoImplicit false
namespace AspisR1.FJh_GroupBounds
open Aeneas Aeneas.Std Result WP
theorem value (g start stop : Usize) (hg : g.val<4)
    (rs : (4#usize*g : Result Usize)=ok start)
    (re : (start+4#usize : Result Usize)=ok stop) :
    start.val=4*g.val ∧ stop.val=4*g.val+4 ∧ start.val≤stop.val ∧ stop.val≤16 := by
  have hmax := Usize.cMax_bound_concrete.1
  have sm : (4#usize*g : Result Usize) ⦃x=>x.val=4*g.val⦄ := by
    apply UScalar.mul_spec
    scalar_tac
  obtain ⟨s,hs,vs⟩ := WP.spec_imp_exists sm
  have es : s=start := Result.ok.inj (hs.symm.trans rs)
  subst s
  have se : (start+4#usize : Result Usize) ⦃x=>x.val=start.val+4⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨e,he,ve⟩ := WP.spec_imp_exists se
  have ee : e=stop := Result.ok.inj (he.symm.trans re)
  subst e
  exact ⟨vs,by omega,by omega,by omega⟩
#print axioms value
end AspisR1.FJh_GroupBounds
