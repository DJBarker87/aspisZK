import PV_LIB_A_V2Neutral14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_V2TraceTransport14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable
open PV_LIB_A_PrefixMachine11

theorem step (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State) (quiet : Quiet P s) :
    PV_LIB_StoreActionTable.step C K P resources encode H values s = PV_THR2_IntrinsicState.step C K P H s := by
  have source := PV_LIB_A_PrefixMachine11.step C K P resources encode H values s quiet
  rw [PV_LIB_A_V2Neutral14.successor_step C K P resources encode H values s quiet.1] at source
  exact congrArg SourceState.base source

/-- ONE trace-indexed induction to original v2. Existing source-segment proofs
are reused by name. The certificate includes every intervening state and reply;
endpoint output equality alone does not license this transport. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (n : Nat) (s : State)
    (trace : Trace C K P H n s) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values n s =
      PV_THR2_IntrinsicState.advance C K P H n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    change PV_LIB_StoreActionTable.advance C K P resources encode H values n
      (PV_LIB_StoreActionTable.step C K P resources encode H values s) = _
    rw [step C K P resources encode H values s trace.1]
    exact ih _ trace.2

/-- Full histories agree only under the proved finite trace certificate. The
phase is none throughout this trace. No unconditional phase projection is used. -/
theorem successor (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (n : Nat) (s : State)
    (trace : Trace C K P H n s) :
    PV_LIB_A_PrefixMachine11.advance C K P resources encode H values n ⟨s,none⟩ =
      ⟨PV_LIB_StoreActionTable.advance C K P resources encode H values n s,none⟩ := by
  rw [PV_LIB_A_PrefixMachine11.run C K P resources encode H values n s trace,
    run C K P resources encode H values n s trace]

#print axioms step
#print axioms run
#print axioms successor
end PV_LIB_A_V2TraceTransport14
