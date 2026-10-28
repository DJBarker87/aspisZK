import NDO_JGn_FullNumeric
import NDO_JGn_LeadingNumeric
import NDO_JGl_InternalNumeric
import RPv_FJh_Native07RawValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_PoseidonNumeric
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)

theorem model : FJh_Native07RawValue.model JGl_NumericData.openings JGl_NumericData.sops=
    decoded JGl_NumericData.poseidon := by
  funext g
  unfold FJh_Native07RawValue.model
  dsimp only [JGl_NumericData.openings,JGl_NumericData.sops]
  erw [JGl_LeadingMath.value,JGn_FullMath.value,JGl_InternalNumeric.model]
  fin_cases g <;> jgl_words
#print axioms model

theorem identified (out : Array field.QM31 4#usize)
    (run : state_only_poseidon.evaluate_state_only_poseidon_oracle_projected
      JGl_NumericData.openings JGl_NumericData.sops=ok out) : out=JGl_NumericData.poseidon := by
  have value := FJh_Native07RawValue.value JGl_NumericData.openings JGl_NumericData.sops out
    JGl_NumericCanonical.a JGl_NumericCanonical.b JGl_NumericCanonical.c
    JGl_NumericCanonical.low (JGl_NumericCanonical.block _ (by simp [JGl_NumericData.sops,JGl_NumericData.block])) run
  exact JGl_ArrayIdentity.value out JGl_NumericData.poseidon value.1 JGl_NumericCanonical.poseidon
    (value.2.trans model)
#print axioms identified
end AspisR1.JGn_PoseidonNumeric
end
