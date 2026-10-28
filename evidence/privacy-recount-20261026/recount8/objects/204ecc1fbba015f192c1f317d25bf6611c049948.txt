import R1Z.ProverRwSuccessPowerTotal
import R1Z.ProverCommitM31Ops48
set_option autoImplicit false
namespace R1Z.ProverRwSuccessPowerExact
open Aeneas Aeneas.Std Result ControlFlow
open ProverCommitM31Ops48

theorem bit_val (exp : U64) : (exp &&& 1#u64).val=exp.val%2 := by
  change (exp.bv &&& (1#u64).bv).toNat=exp.val%2
  rw [BitVec.toNat_and]
  change exp.val &&& 1=exp.val%2
  exact Nat.and_two_pow_sub_one_eq_mod _ 1

theorem power_step {K : Type} [CommMonoid K] (a b : K) (n : Nat) :
    (a*b^(n%2))*(b*b)^(n/2)=a*b^n := by
  rw [←pow_two,←pow_mul,mul_assoc,←pow_add]
  congr 1
  congr 1
  omega

theorem exact_result (n : Nat) (exp : U64) (he : exp.val=n)
    (base acc : U32) (ha : canonical acc) :
    ∃ z : U32, ProverRwSuccessPowerTotal.S.pow exp base acc=.ok z ∧
      canonical z ∧ decode z=decode acc*decode base^n := by
  induction n using Nat.strong_induction_on generalizing exp base acc with
  | h n ih =>
    rw [ProverRwSuccessPowerTotal.pow_unfold]
    unfold ProverRwSuccessPowerTotal.S.body ProverRwSuccessInverseSource.field.M31.pow_loop.body
    by_cases hz : exp > 0#u64
    · rw [if_pos hz]
      let r := exp &&& 1#u64
      let d := U64.wrapping_shr exp 1#u32
      have hrv : r.val=n%2 := by rw [bit_val,he]
      have hdv : d.val=n/2 := by rw [ProverRwSuccessPowerTotal.shift,he]
      have small : n/2<n := by
        have pos : 0<n := by change (0#u64).val<exp.val at hz; change 0<exp.val at hz; omega
        omega
      obtain ⟨square,hs,hcs,hvs⟩ := mul_exact base base
      have next : ∃ a : U32,
          (if r=1#u64 then ProverRwSuccessInverseSource.field.M31.mul acc base else .ok acc)=.ok a ∧
          canonical a ∧ decode a=decode acc*decode base^(n%2) := by
        by_cases bit : n%2=1
        · have one : r=1#u64 := UScalar.eq_of_val_eq (by simpa [bit] using hrv)
          obtain ⟨a,hm,hca,hva⟩ := mul_exact acc base
          exact ⟨a,by rw [if_pos one];exact hm,hca,by rw [bit,pow_one];exact hva⟩
        · have zero : n%2=0 := by omega
          have notone : r≠1#u64 := by intro h; rw [h] at hrv; change 1=n%2 at hrv; omega
          exact ⟨acc,by rw [if_neg notone],ha,by rw [zero,pow_zero,mul_one]⟩
      obtain ⟨a,hm,hca,hva⟩ := next
      obtain ⟨z,ho,hcz,hvz⟩ := ih (n/2) small d hdv square a hca
      refine ⟨z,?_,hcz,?_⟩
      · dsimp only [r] at hm
        dsimp only [d] at ho
        simp only [lift,bind_tc_ok,hm,hs,ho]
      · rw [hvz,hva,hvs,power_step]
    · rw [if_neg hz]
      have zero : n=0 := by change ¬(0#u64).val<exp.val at hz; change ¬0<exp.val at hz; omega
      exact ⟨acc,rfl,ha,by rw [zero,pow_zero,mul_one]⟩
#print axioms bit_val
#print axioms power_step
#print axioms exact_result
end R1Z.ProverRwSuccessPowerExact
