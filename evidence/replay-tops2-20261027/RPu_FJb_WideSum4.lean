import RPu_FJa_PoseidonPow5
set_option autoImplicit false
namespace AspisR1.FJb_WideSum4
open Aeneas Aeneas.Std Result WP
def wide (x : U32) : U64 := core.convert.num.FromU64U32.from x
theorem wide_val (x : U32) : (wide x).val=x.val := by
  change (x.bv.setWidth 64).toNat=x.bv.toNat
  apply BitVec.toNat_setWidth_of_le
  decide
def source (a b c d : U32) : Result U64 := do
  let ab ← wide a+wide b
  let abc ← ab+wide c
  abc+wide d
/-- Exact checked addition of four actual U32 limbs; bounds are derived. -/
theorem value (a b c d : U32) :
    ∃ out,source a b c d=ok out ∧
      out.val=a.val+b.val+c.val+d.val ∧ out.val < 2^34 := by
  have ha : a.val < 2^32 := a.bv.isLt
  have hb : b.val < 2^32 := b.bv.isLt
  have hc : c.val < 2^32 := c.bv.isLt
  have hd : d.val < 2^32 := d.bv.isLt
  have hab : (wide a+wide b : Result U64) ⦃z=>z.val=(wide a).val+(wide b).val⦄ := by
    apply UScalar.add_spec
    simp only [wide_val]
    scalar_tac
  obtain ⟨ab,rab,vab⟩ := WP.spec_imp_exists hab
  have habc : (ab+wide c : Result U64) ⦃z=>z.val=ab.val+(wide c).val⦄ := by
    apply UScalar.add_spec
    simp only [wide_val] at *
    scalar_tac
  obtain ⟨abc,rabc,vabc⟩ := WP.spec_imp_exists habc
  have habcd : (abc+wide d : Result U64) ⦃z=>z.val=abc.val+(wide d).val⦄ := by
    apply UScalar.add_spec
    simp only [wide_val] at *
    scalar_tac
  obtain ⟨out,rout,vout⟩ := WP.spec_imp_exists habcd
  refine ⟨out,?_,?_,?_⟩
  · simp only [source,rab,rabc,rout,bind_tc_ok]
  · simp only [vout,vabc,vab,wide_val]
  · simp only [wide_val] at *
    omega
#print axioms wide_val
#print axioms value
end AspisR1.FJb_WideSum4
