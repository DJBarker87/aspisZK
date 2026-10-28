import R1Z.ProverRwP6QuarticTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6WideTotal
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
abbrev W := field.wide_exact.WideExact
theorem mul (a b : W) : ∃ c, field.wide_exact.WideExact.mul a b = ok c := by
  obtain ⟨ac,hac⟩ := ProverRwP6QuarticTotal.mul a.c0 b.c0
  obtain ⟨bd,hbd⟩ := ProverRwP6QuarticTotal.mul a.c1 b.c1
  obtain ⟨q,hq⟩ := ProverRwP6QuarticTotal.add a.c0 a.c1
  obtain ⟨r,hr⟩ := ProverRwP6QuarticTotal.add b.c0 b.c1
  obtain ⟨cross,hcross⟩ := ProverRwP6QuarticTotal.mul q r
  obtain ⟨u,hu⟩ := ProverRwP6QuarticTotal.mul_u bd
  obtain ⟨v,hv⟩ := ProverRwP6QuarticTotal.add ac u
  obtain ⟨w,hw⟩ := ProverRwP6QuarticTotal.sub cross ac
  obtain ⟨z,hz⟩ := ProverRwP6QuarticTotal.sub w bd
  simp only [field.wide_exact.WideExact.mul,hac,hbd,hq,hr,hcross,hu,hv,hw,hz,bind_tc_ok]
  exact ⟨_,rfl⟩
-- Exact retained dictionary maps; no native/ABI association claimed here.
theorem dictionary_mul (a b : ProverRwDictionaryTower.W) :
    ∃ c, ProverRwDictionaryTower.wMul a b = ok c := by
  obtain ⟨c,hc⟩ := mul (ProverRwDictionaryTower.toW a) (ProverRwDictionaryTower.toW b)
  unfold ProverRwDictionaryTower.wMul
  rw [hc]
  exact ⟨_,rfl⟩
theorem dictionary_qadd (a b : ProverRwDictionaryTower.Q) :
    ∃ c, ProverRwDictionaryTower.qAdd a b = ok c := by
  obtain ⟨c,hc⟩ := ProverRwP6QuarticTotal.add (ProverRwDictionaryTower.toQ a) (ProverRwDictionaryTower.toQ b)
  unfold ProverRwDictionaryTower.qAdd
  rw [hc]
  exact ⟨_,rfl⟩
#print axioms mul
#print axioms dictionary_mul
#print axioms dictionary_qadd
end R1Z.ProverRwP6WideTotal
