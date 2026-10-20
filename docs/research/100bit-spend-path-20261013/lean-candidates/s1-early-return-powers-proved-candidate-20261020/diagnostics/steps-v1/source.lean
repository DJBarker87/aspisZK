import LoopPowersZeroCandidate
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1LoopPowers
@[rust_loop_body]
def weights.early_powers_loop.body
  {N : Std.Usize} (x : field.WideExact) (out : Array field.WideExact N)
  (p : field.WideExact) (i : Std.Usize) :
  Result (ControlFlow ((Array field.WideExact N) × field.WideExact ×
    Std.Usize) (Array field.WideExact N))
  := do
  if i < N
  then
    let (_, index_mut_back) ← Array.index_mut_usize out i
    let i1 ← i + 1#usize
    if i1 = N
    then let out1 := index_mut_back p
         ok (done out1)
    else
      let p1 ← field.WideExact.mul p x
      let a := index_mut_back p
      ok (cont (a, p1, i1))
  else ok (done out)

/-- [aspis_r1_current_powers::weights::powers]: loop 0:
    Source: 'lib.rs', lines 59:1-66:1
    Visibility: public -/
@[rust_loop]
def weights.early_powers_loop
  {N : Std.Usize} (x : field.WideExact) (out : Array field.WideExact N)
  (p : field.WideExact) (i : Std.Usize) :
  Result (Array field.WideExact N)
  := do
  loop
    (fun (out1, p1, i1) => weights.early_powers_loop.body x out1 p1 i1)
    (out, p, i)

/-- [aspis_r1_current_powers::weights::powers]:
    Source: 'lib.rs', lines 55:0-66:1
    Visibility: public -/
def weights.early_powers
  (N : Std.Usize) (x : field.WideExact) :
  Result (Array field.WideExact N)
  := do
  let out := Array.repeat N field.WideExact.ZERO
  weights.early_powers_loop x out field.WideExact.ONE 0#usize


theorem early_body_step {N : Usize} (x p : field.WideExact) (a : Array field.WideExact N)
    (i : Usize) (hi : i.val < N.val) (hx : Canonical x) (hp : Canonical p) :
    ∃ i', i'.val = i.val+1 ∧
      ((i'=N ∧ weights.early_powers_loop.body x a p i = .ok (.done (a.set i p))) ∨
       (i'≠N ∧ ∃ p', weights.early_powers_loop.body x a p i = .ok (.cont (a.set i p,p',i')) ∧
         Canonical p' ∧ decode p' = decode p * decode x)) := by
  obtain ⟨out,hmut,hspec⟩ := WP.spec_imp_exists
    (Array.index_mut_usize_spec a i (by simpa [a.property] using hi))
  rcases out with ⟨old,back⟩
  rcases hspec with ⟨_,hback⟩
  subst back
  have hNmax : N.val ≤ Usize.max := by
    have hN : N.val < 2^Usize.numBits := by
      simpa [Usize.numBits,UScalarTy.Usize_numBits_eq] using N.hBounds
    have hmax : Usize.max+1=2^Usize.numBits := by
      rw [Usize.numBits]; exact Usize.max_succ_eq_pow
    omega
  have hiBound : i.val+1 ≤ Usize.max := by omega
  have haddSpec : (i+1#usize : Result Usize) ⦃ j => j.val=i.val+1 ⦄ := by
    apply UScalar.add_spec
    have hone : (1#usize).val=1 := by scalar_tac
    simpa only [hone,UScalar.max_USize_eq] using hiBound
  obtain ⟨i',ha,hi'⟩ := WP.spec_imp_exists haddSpec
  have hlt : i<N := by simpa only [UScalar.lt_equiv] using hi
  refine ⟨i',hi',?_⟩
  by_cases he : i'=N
  · left
    refine ⟨he,?_⟩
    simp only [weights.early_powers_loop.body,hlt,ite_true,hmut,ha,bind_tc_ok,he]
  · right
    obtain ⟨p',hm,hc,hp'⟩ := mul_total_exact p x hp hx
    refine ⟨he,p',?_,hc,hp'⟩
    simp only [weights.early_powers_loop.body,hlt,ite_true,hmut,ha,bind_tc_ok,he,ite_false,hm]

theorem early_body_done {N : Usize} (x p : field.WideExact) (a : Array field.WideExact N)
    (i : Usize) (hi : N.val ≤ i.val) :
    weights.early_powers_loop.body x a p i = .ok (.done a) := by
  have hn : ¬i<N := by simpa only [UScalar.lt_equiv] using Nat.not_lt.mpr hi
  simp only [weights.early_powers_loop.body,hn,ite_false]
#print axioms early_body_step
#print axioms early_body_done
end AspisR1LoopPowers
