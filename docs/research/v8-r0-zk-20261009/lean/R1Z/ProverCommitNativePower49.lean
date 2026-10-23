import R1Z.ProverCommitPowerStep49
/-! Induction on the shrinking exponent of the actual owned power reference. -/
set_option autoImplicit false
namespace R1Z.ProverCommitNativePower49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)

theorem power (n : Nat) (exp : U8) (he : exp.val=n) (base acc : Old.Q)
    (hb : Canonical base) (ha : Canonical acc) :
    ∃ z : Old.Q, kernels.power (ProverCommitNativeQ48.source base) exp (ProverCommitNativeQ48.source acc)=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=decode acc*decode base^n := by
  induction n using Nat.strong_induction_on generalizing exp base acc with
  | h n ih =>
    by_cases hn : n=0
    · have hz : exp=0#u8 := by apply UScalar.eq_of_val_eq;simpa only [he,hn,show (0#u8).val=0 from rfl]
      refine ⟨acc,?_,ha,?_⟩
      · rw [kernels.power,hz];rfl
      · simp only [hn,pow_zero,mul_one]
    · have hz : exp≠0#u8 := by intro h0;have hv := congrArg (fun a : U8 => a.val) h0;change exp.val=0 at hv;omega
      have hlt : n/2<n := Nat.div_lt_self (by omega) (by decide)
      have hs : (U8.wrapping_shr exp 1#u32).val=n/2 := by rw [ProverCommitPowerStep49.shift,he]
      obtain ⟨sq,hsq,hcsq,hvsq⟩ := ProverCommitNativeQSquare49.square base hb
      have next : ∃ a : Old.Q,
          (if ((exp &&& 1#u8) != 0#u8) then
             field.QM31.mul (ProverCommitNativeQ48.source acc) (ProverCommitNativeQ48.source base)
           else ok (ProverCommitNativeQ48.source acc))=ok (ProverCommitNativeQ48.source a) ∧
          Canonical a ∧ decode a=(if n%2≠0 then decode acc*decode base else decode acc) := by
        rw [ProverCommitPowerStep49.condition,he]
        by_cases hmod : n%2≠0
        · obtain ⟨a,hm,hca,hva⟩ := ProverCommitNativeQ48.mul acc base ha hb
          exact ⟨a,by simp [hmod,hm],hca,by simp [hmod,hva]⟩
        · exact ⟨acc,by simp only [hmod,decide_false,Bool.false_eq_true,if_false],ha,by simp only [hmod,if_false]⟩
      obtain ⟨a,hm,hca,hva⟩ := next
      obtain ⟨z,hr,hcz,hvz⟩ := ih (n/2) hlt _ hs sq a hcsq hca
      refine ⟨z,?_,hcz,?_⟩
      · rw [kernels.power]
        simp only [hz,if_false,lift,bind_tc_ok,hm,hsq]
        exact hr
      · rw [hvz,hva,hvsq]
        exact ProverCommitPowerStep49.step _ _ n

#print axioms power
end R1Z.ProverCommitNativePower49
