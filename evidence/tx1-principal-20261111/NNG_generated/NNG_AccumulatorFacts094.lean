import LIBC_AccNew
import LIBC_WeightsNew
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_AccumulatorFacts094
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port2_Initial
/-- Fields of the SAME successful constructor; reservation success is a
conclusion, including on the arbitrary original Env reservation. -/
theorem native_fields (env : RSL.Env) (a : verifier.Accumulator)
 (run : LIBC_AccNew.model env=ok (.Ok a)) :
 env.reservation=true ∧ a.weights.val=List.replicate 64 zeroK ∧
 a.rhs=zeroE ∧ a.power=oneK ∧ a.next=0#usize := by
 change Port3_Initial.constructor env.reservation .S2=ok (.Ok a) at run
 rw [Port3_Initial.constructor_shell] at run
 obtain ⟨weights,success,same⟩ := (newS2_success _ a).mp run
 obtain ⟨reserved,contents⟩ := CheckpointBytes3Allocation.filled_success_content
  env.reservation 64#usize zeroK weights success
 subst a
 exact ⟨reserved,contents,rfl,rfl,rfl⟩
#print axioms native_fields
end AspisR1.NNG_AccumulatorFacts094
