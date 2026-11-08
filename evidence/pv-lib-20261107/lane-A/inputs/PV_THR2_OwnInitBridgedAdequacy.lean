import PV_THR2_OwnInitInterpreterBridged
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitBridgedAdequacy
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
/-- Concrete Recount14 obligation for the NEW14756 interpretation.
sourceStep must be the frozen source/binary step projected with the same
source store, OWNER instrumentation and image loader environment. The other
side is FIXED to OwnInitInterpreterBridged.step, not an arbitrary function.
Both initial call and pending retry action shapes are included. Equality of
the entire state retains every answer, source cell, world effect, event and
suspended configuration. No Shape, decode-success or returned-case hypothesis
narrows this obligation. No theorem assumes or proves it in this session. -/
def InterpretationAdequacy14756 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (sourceStep : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent →
      PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  ∀ q c, q.current.status = .running c → PV_THR2_OwnInitAction.selected c = true →
    sourceStep q = PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H q
end PV_THR2_OwnInitBridgedAdequacy
