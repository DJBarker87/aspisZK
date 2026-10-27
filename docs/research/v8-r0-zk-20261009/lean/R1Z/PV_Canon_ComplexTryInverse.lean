import R1Z.PV_Canon_Result
import R1Z.PV_Canon_Reduce
import R1Z.ProverRwSuccessInverseSource
import R1Z.PV_Join_ParseQuarticCanonical5
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 def SomeC (o : Option aspis_core.field.CM31) : Prop := ∀ z, o=some z → C z
 theorem release_mul_safe (a b : U32) : Safe M (AspisR1ProducerRelease47.field.M31.mul a b) := by
  obtain ⟨z,hz,hc,_⟩ := ProverCommitM31Ops48.mul_exact a b
  exact safe_of_total ⟨z,hz,hc⟩
/-- The last two scalar products reduce every successful output coordinate.
No nonzero or inverse-success premise is required for this range statement. -/
 theorem complex_try_inverse_safe (x : aspis_core.field.CM31) :
    Safe SomeC (ProverRwSuccessInverseSource.field.CM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv x) := by
  unfold ProverRwSuccessInverseSource.field.CM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv
  apply safe_bind_any; intro aa
  apply safe_bind_any; intro bb
  apply safe_bind_any; intro norm
  apply safe_bind_any; intro inverse
  cases inverse with
  | none =>
    simpa only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok,Safe,SomeC,PV_Join_ResultInvariant5.Safe]
      using PV_Join_ParseQuarticCanonical5.none_residual C
  | some inv =>
    simp only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok]
    apply safe_bind M SomeC _ _ (release_mul_safe x.a inv)
    intro a ha
    apply safe_bind_any; intro nb
    apply safe_bind M SomeC _ _ (release_mul_safe nb inv)
    intro b hb
    apply safe_ok
    intro z hz; cases hz; exact ⟨ha,hb⟩
#print axioms release_mul_safe
#print axioms complex_try_inverse_safe
end R1Z.PV_Canon
