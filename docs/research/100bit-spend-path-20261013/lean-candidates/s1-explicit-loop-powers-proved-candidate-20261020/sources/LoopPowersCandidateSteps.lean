import LoopPowersCandidateModel
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1LoopPowers

theorem one_canonical : Canonical field.WideExact.ONE := by
  norm_num [Canonical,toOld,toOldQM,field.WideExact.ONE,field.QM31.ONE,field.QM31.ZERO,
    AspisR1PowersConcreteMul.Canonical,AspisR1PowersConcreteMul.toWide,AspisR1PowersConcreteMul.toQM,
    AspisR1CurrentWideMul.CanonicalWide,AspisR1CurrentWideMul.CanonicalQM,AspisR1CurrentWideMul.CanonicalCM,
    AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
    AspisR1.ExtractedCurrentTowerAdd.P,AspisR1.ExtractedCurrentM31AddSub.P]

theorem one_decode : decode field.WideExact.ONE = 1 := by
  apply QuadraticAlgebra.ext
  all_goals apply QuadraticAlgebra.ext
  all_goals apply QuadraticAlgebra.ext
  all_goals norm_num [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero,decode,toOld,toOldQM,field.WideExact.ONE,field.QM31.ONE,field.QM31.ZERO,
    AspisR1PowersExactProduct.decode,AspisR1PowersExactProduct.toFull,AspisR1PowersExactProduct.toFullQM,
    AspisR1CurrentWide.Proof.decodeWide,AspisR1CurrentWide.Proof.decodeQM,AspisR1CurrentWide.Proof.toQM,
    AspisR1CurrentWide.Proof.toCM,AspisR1.ExtractedCurrentQM31Exact.decode]

theorem loop_body_step {N : Usize} (x p : field.WideExact) (a : Array field.WideExact N)
    (i : Usize) (hi : i.val < N.val) (hx : Canonical x) (hp : Canonical p) :
    ∃ p' i', weights.powers_loop.body x a p i = .ok (.cont (a.set i p,p',i')) ∧
      Canonical p' ∧ decode p' = decode p * decode x ∧ i'.val = i.val + 1 := by
  obtain ⟨a',ha',heq⟩ := WP.spec_imp_exists (Array.update_spec a i p (by simpa [a.property] using hi))
  subst a'
  obtain ⟨p',hm,hc,he⟩ := mul_total_exact p x hp hx
  have hNmax : N.val ≤ Usize.max := by
    have hN : N.val < 2^Usize.numBits := by
      simpa [Usize.numBits,UScalarTy.Usize_numBits_eq] using N.hBounds
    have hmax : Usize.max + 1 = 2^Usize.numBits := by
      rw [Usize.numBits]; exact Usize.max_succ_eq_pow
    omega
  have hiBound : i.val+1 ≤ Usize.max := by omega
  have haddSpec : (i+1#usize : Result Usize) ⦃ j => j.val=i.val+1 ⦄ := by
    apply UScalar.add_spec
    have hone : (1#usize).val=1 := by scalar_tac
    simpa only [hone,UScalar.max_USize_eq] using hiBound
  obtain ⟨i',ha,hi'⟩ := WP.spec_imp_exists haddSpec
  refine ⟨p',i',?_,hc,he,hi'⟩
  have hlt : i < N := by simpa only [UScalar.lt_equiv] using hi
  simp only [weights.powers_loop.body,hlt,ite_true,ha',hm,ha,bind_tc_ok]

theorem loop_body_done {N : Usize} (x p : field.WideExact) (a : Array field.WideExact N)
    (i : Usize) (hi : N.val ≤ i.val) :
    weights.powers_loop.body x a p i = .ok (.done a) := by
  have hn : ¬i<N := by simpa only [UScalar.lt_equiv] using Nat.not_lt.mpr hi
  simp only [weights.powers_loop.body,hn,ite_false]

#print axioms one_canonical
#print axioms one_decode
#print axioms loop_body_step
#print axioms loop_body_done
end AspisR1LoopPowers
