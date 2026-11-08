import PV_FN_THREAD_f6Joins
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F6DeliveryTransportV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f6Interfaces PV_FN_THREAD_f6Joins
/-- Local source agreement only while this provider row has not delivered.
No finite-delivery/termination witness and no post-delivery agreement is needed.
This is a proof-local predicate, not a MachineSpec or endpoint premise. Actual
callee-table and named native-semantics bindings are still to be discharged. -/
def Agreement (M N : Machine PV_RJ4IDB.NativeEvent)
    (y : Entry PV_RJ4IDB.NativeEvent) : Prop :=
  ∀ k, BeforeDelivery N y (k+1) →
    PV_THR2_TableIntrinsic.Agree N.programs M.programs (run N y k) ∧
      PV_THR2_InterpreterAgreement.NativeAgree N.handler M.handler (run N y k)

/-- Bind the existing SINGLE symbolic induction directly to f6's literal
PrefixIdentity type. This removes the artificial need to find a finite delivery
cutoff. It includes infinite prefixes, every failure and the consumed pending
prefix, and makes no claim of GlobalOriginalTransport or actual-row closure. -/
theorem prefix_identity (M N : Machine PV_RJ4IDB.NativeEvent)
    (y : Entry PV_RJ4IDB.NativeEvent)
    (carrier : M.carrier = N.carrier) (control : M.control = N.control)
    (same : Agreement M N y) : PrefixIdentity M N y := by
  refine ⟨carrier,control,?_⟩
  intro n before
  unfold PV_FN_THREAD_f6Interfaces.run
  rw [carrier,control]
  exact PV_THR2_InterpreterAgreement.run N.carrier N.control N.programs M.programs
    N.handler M.handler n (entry y) (fun k hk =>
      same k (before_delivery_mono N y n (k+1) before (Nat.succ_le_of_lt hk)))

#print axioms prefix_identity
end PV_LIB_A_F6DeliveryTransportV2
