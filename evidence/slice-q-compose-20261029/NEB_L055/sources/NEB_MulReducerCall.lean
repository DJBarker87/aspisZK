import NEB_ReducerCall
import NBG_InverseBridge
import JFv_RawExtractedSemanticCallOpsV20
set_option autoImplicit false
namespace NEB_MulReducerCall
open Aeneas Aeneas.Std Result AspisR1

def product (x y : U32) : U64 :=
  U64.wrapping_mul (UScalar.cast .U64 x) (UScalar.cast .U64 y)

theorem domain (x y : U32) : NEB_ReducerCall.PacketDomain (product x y) :=
  NEB_ReducerCall.all_domain _

theorem input_value (x y : U32) : (product x y).val=x.val*y.val :=
  LPf_BaseMultiply.word_product x y

/-- Actual translated caller body, same input to the private reducer, and
same scalar reply. No canonical operand assumption is introduced. -/
theorem callsite (x y : U32) :
    FIo_Native.aspis_core.field.M31.mul x y=
      FIo_Native.aspis_core.field.reduce_u64 (product x y) := by
  simp only [FIo_Native.aspis_core.field.M31.mul,product,lift,bind_tc_ok]
  generalize hr : FIo_Native.aspis_core.field.reduce_u64 (product x y)=r
  cases r <;> rfl

theorem value (x y : U32) : ∃ z,
    FIo_Native.aspis_core.field.M31.mul x y=ok z ∧
    FIo_Native.aspis_core.field.reduce_u64 (product x y)=ok z ∧
    z.val=(x.val*y.val)%2147483647 ∧ z.val<2147483647 := by
  obtain ⟨z,run,v,cz⟩ := LPf_CoreReduction.source (product x y)
  exact ⟨z,(callsite x y).trans run,run,by rw [input_value] at v;exact v,cz⟩

theorem state_effects {S Event : Type} (state : S) (x y : U32) : ∃ z,
    NEB_ReducerCall.withState (Event:=Event) state
      (FIo_Native.aspis_core.field.M31.mul x y)=ok (z,state,[]) ∧
    NEB_ReducerCall.withState (Event:=Event) state
      (FIo_Native.aspis_core.field.reduce_u64 (product x y))=ok (z,state,[]) ∧
    z.val=(x.val*y.val)%2147483647 ∧ z.val<2147483647 := by
  obtain ⟨z,run,reducer,v,cz⟩ := value x y
  exact ⟨z,by simp only [NEB_ReducerCall.withState,run,bind_tc_ok],
    by simp only [NEB_ReducerCall.withState,reducer,bind_tc_ok],v,cz⟩

#print axioms domain
#print axioms input_value
#print axioms callsite
#print axioms value
#print axioms state_effects
#print axioms NBG_InverseBridge.mul_eq_probe
#print axioms AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.generated_m31_mul_eq_probe
end NEB_MulReducerCall
