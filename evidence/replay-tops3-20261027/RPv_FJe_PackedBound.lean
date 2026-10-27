import RPv_FJe_RawReference
import RPv_FJb_WideSum4
set_option autoImplicit false
namespace AspisR1.FJe_PackedBound
open Aeneas Aeneas.Std Result FIq_Native
open AspisV8R15.ExactTowerBase (P)
/-- The original seven-modulus offset and its machine bound;no recurrence or
permutation is evaluated. -/
theorem value : ∃ bound : U64,
    state_only_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND=ok bound ∧
      bound.val=7*P ∧ 8*bound.val<2^64 := by
  let p := FJb_WideSum4.wide field.P
  have vp : p.val=P := by rw [FJb_WideSum4.wide_val];norm_num [field.P,P]
  have h7 : (7#u64).val=7 := rfl
  have hb : (7#u64).val*p.val<2^64 := by rw [h7,vp];norm_num [P]
  obtain ⟨bound,run,vb⟩ := ExtractedMaskReducerOps.mul_success (7#u64) p hb
  have vbound : bound.val=7*P := by simpa only [h7,vp] using vb
  refine ⟨bound,?_,vbound,?_⟩
  · unfold state_only_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND
    exact run
  · rw [vbound]
    norm_num [P]
#print axioms value
end AspisR1.FJe_PackedBound
