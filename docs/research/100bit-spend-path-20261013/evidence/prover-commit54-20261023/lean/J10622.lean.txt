import AspisR1ProducerRelease47.EncoderNodes54
import R1Z.ProverCommitNativeC49
/-! Binary CM31 power with arbitrary canonical inputs and full exponent range. -/
set_option autoImplicit false
namespace R1Z.ProverCommitEncoderPower54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitNativeC49

attribute [local irreducible] source

theorem power_step {K : Type} [CommMonoid K] (a b : K) (n : Nat) :
    (a*b^(n%2))*(b*b)^(n/2)=a*b^n := by
  rw [←pow_two,←pow_mul,mul_assoc,←pow_add]
  congr 1
  congr 1
  omega

theorem exact_result (n : Nat) (exp : U64) (he : exp.val=n)
    (base acc : Old.C) (hb : Canonical base) (ha : Canonical acc) :
    ∃ z : Old.C, nodes54.pow (source base) exp (source acc)=ok (source z) ∧
      Canonical z ∧ value z=value acc*value base^n := by
  induction n using Nat.strong_induction_on generalizing exp base acc with
  | h n ih =>
    by_cases hn : n=0
    · have hz : exp=0#u64 := by scalar_tac
      refine ⟨acc,?_,ha,?_⟩
      · rw [nodes54.pow,hz];rfl
      · rw [hn,pow_zero,mul_one]
    · have hne : exp≠0#u64 := by scalar_tac
      obtain ⟨r,hr,hrv⟩ := WP.spec_imp_exists (UScalar.rem_spec exp (show (2#u64).val≠0 by decide))
      obtain ⟨d,hd,hdv,_⟩ := UScalar.div_bv_spec (y:=2#u64) exp (by decide)
      have hrv' : r.val=n%2 := by simpa only [he,show (2#u64).val=2 from rfl] using hrv
      have hdv' : d.val=n/2 := by simpa only [he,show (2#u64).val=2 from rfl] using hdv
      obtain ⟨square,hsquare,hcsquare,hdsquare⟩ := mul base base hb hb
      have hnext : ∃ next : Old.C,
          (if r=1#u64 then field.CM31.mul (source acc) (source base) else ok (source acc))=ok (source next) ∧
          Canonical next ∧ value next=value acc*value base^(n%2) := by
        by_cases hbit : n%2=1
        · have hrone : r=1#u64 := by scalar_tac
          obtain ⟨next,hnext,hcnext,hdnext⟩ := mul acc base ha hb
          exact ⟨next,by rw [hrone,if_pos rfl];exact hnext,hcnext,by rw [hbit,pow_one];exact hdnext⟩
        · have hrzero : n%2=0 := by omega
          have hrnot : r≠1#u64 := by scalar_tac
          exact ⟨acc,by rw [if_neg hrnot],ha,by rw [hrzero,pow_zero,mul_one]⟩
      obtain ⟨next,hnext,hcnext,hdnext⟩ := hnext
      obtain ⟨z,hz,hcz,hdz⟩ := ih (n/2) (by omega) d hdv' square next hcsquare hcnext
      refine ⟨z,?_,hcz,?_⟩
      · rw [nodes54.pow]
        simp only [hne,if_false,hr,bind_tc_ok,hnext,hsquare,hd,hz]
      · rw [hdz,hdnext,hdsquare,power_step]

#print axioms power_step
#print axioms exact_result
end R1Z.ProverCommitEncoderPower54
