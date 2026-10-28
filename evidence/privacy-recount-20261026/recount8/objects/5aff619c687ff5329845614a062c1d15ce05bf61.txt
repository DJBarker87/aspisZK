import R1Z.PV_RunJoin_WeightScalar46
import R1Z.ProverCommitRelease47
import R1Z.ProverCommitPrimitive47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightNormalize46
open Aeneas Aeneas.Std Result

theorem complete (x : U32) :
    x % AspisR1ProducerRelease47.field.P=
      ok (PV_B2_C_251FieldValue.aspis_core.field.ct.reduce64 (UScalar.cast .U64 x)) := by
  obtain ⟨z,hz,hv,_⟩ := AspisR1.ExtractedCurrentReducer.current_reduce_mod (UScalar.cast .U64 x)
  have hc : AspisR1ProducerChecked47.field.reduce_u64 (UScalar.cast .U64 x)=ok z := by
    rw [ProverCommitPrimitive47.reduce]
    exact hz
  have hr : AspisR1ProducerRelease47.field.reduce_u64 (UScalar.cast .U64 x)=ok z :=
    ProverCommitRelease47.reduce _ z hc
  have he : PV_B2_C_251FieldValue.aspis_core.field.ct.reduce64 (UScalar.cast .U64 x)=z :=
    Result.ok.inj ((PV_RunJoin_WeightScalar46.reduce _).symm.trans hr)
  have hb : AspisR1ProducerRelease47.field.P.val≠0 := by
    rw [AspisR1ProducerRelease47.field.P]
    decide
  obtain ⟨r,hm,hvr⟩ := WP.spec_imp_exists (UScalar.rem_spec x hb)
  rw [hm]
  apply congrArg Result.ok
  apply UScalar.eq_of_val_eq
  rw [he,hvr,AspisR1ProducerRelease47.field.P]
  change z.val=(UScalar.cast .U64 x).val%2147483647 at hv
  rw [AspisR1.ExtractedCurrentReducer.cast_widen_value] at hv
  exact hv.symm
#print axioms complete
end R1Z.PV_RunJoin_WeightNormalize46
