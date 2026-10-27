import R1Z.PV_Canon_InverseTowerOps
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 def SomeQ (o : Option aspis_core.field.QM31) : Prop := ∀ z, o=some z → Q z
 theorem quartic_try_inverse_safe (x : aspis_core.field.QM31) (hx : Q x) :
    Safe SomeQ (ProverRwSuccessInverseSource.field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv x) := by
  unfold ProverRwSuccessInverseSource.field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv
  apply safe_bind_any; intro r
  apply safe_bind_any; intro aa
  apply safe_bind_any; intro bb
  apply safe_bind_any; intro rb
  apply safe_bind_any; intro norm
  apply safe_bind SomeC SomeQ _ _ (complex_try_inverse_safe norm)
  intro inverse hi
  cases inverse with
  | none =>
    simpa only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      bind_tc_ok,Safe,SomeQ,PV_Join_ResultInvariant5.Safe]
      using PV_Join_ParseQuarticCanonical5.none_residual Q
  | some inv =>
    simp only [ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok]
    have hc : C inv := hi inv rfl
    apply safe_bind C SomeQ _ _ (inverse_cmul_safe x.c0 inv hx.1 hc)
    intro a ha
    apply safe_bind C SomeQ _ _ (inverse_cneg_safe x.c1 hx.2)
    intro nb hnb
    apply safe_bind C SomeQ _ _ (inverse_cmul_safe nb inv hnb hc)
    intro b hb
    apply safe_ok
    intro z hz; cases hz; exact ⟨ha,hb⟩
#print axioms quartic_try_inverse_safe
end R1Z.PV_Canon
