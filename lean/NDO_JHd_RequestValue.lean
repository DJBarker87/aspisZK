import NDO_JHd_RequestPayload
import JHb_RequestBindings
set_option autoImplicit false
namespace AspisR1.JHd_RequestValue
open Aeneas Aeneas.Std Result
open AspisR20Request pool_v1.pair_forest_terminal

def value : PoolV1PairForestTerminalRequestV1 :=
  ⟨AdapterRw.r1_pool_adapter.PROFILE_BINDING,AdapterRw.r1_pool_adapter.RELEASE_BINDING,
    JHb_Programs.pool,.PrivateTransfer JHd_RequestPayment.value⟩

theorem profile_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    value.verifier_profile (Array.repeat 32#usize 0#u8)=ok false := by
  unfold value AdapterRw.r1_pool_adapter.PROFILE_BINDING
  rfl
#print axioms profile_nonzero

theorem release_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    value.verifier_release (Array.repeat 32#usize 0#u8)=ok false := by
  unfold value AdapterRw.r1_pool_adapter.RELEASE_BINDING
  rfl
#print axioms release_nonzero

theorem pool_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    value.pool_program (Array.repeat 32#usize 0#u8)=ok false := by rfl
#print axioms pool_nonzero
end AspisR1.JHd_RequestValue
