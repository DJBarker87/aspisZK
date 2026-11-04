import NFG_FullDot
import NFG_PushComposed
import NFE_WrapperBridge
import NEB_PureFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFG_DotComposed
open Aeneas Aeneas.Std Result NEV_DotCarrier
/-- Complete model G, including failure/divergence. Persistent state and
semantic effects use the existing pure-frame interpretation, as in NFB. -/
theorem one_result_state_effects {State Event : Type} (state : State)
 (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
 (canonical : NEV_DotInputs.Canonical g) (slot : Usize) :
 NEB_PureFrame.run (Event:=Event) state (NFG_FullDot.one q g slot)=
 NEB_PureFrame.run state (FIp_NativeDots.fast_dots.four_dots_one q g slot) :=
 NEB_PureFrame.equality state _ _ (NFG_FullDot.one_result q g canonical slot)

theorem four_result_state_effects {State Event : Type} (state : State)
 (q : Slice U8) (g : NEV_DotInputs.Coefficients) (canonical : NEV_DotInputs.Canonical g) :
 NEB_PureFrame.run (Event:=Event) state (NFG_FullDot.four q g)=
 NEB_PureFrame.run state (NEI_FourWrapper.fast_dots.four_dots q g) :=
 NEB_PureFrame.equality state _ _ (NFG_FullDot.headline q g canonical)

/-- The returned private receiver is the whole modified state; ambient state
and protocol effects are separate from native panic I/O. -/
theorem private_result_state_effects {State Event : Type} (state : State)
 (self : FIo_Native.fast_pairing.canonical.Dot) (a b : FIo_Native.fast_pairing.canonical.Q) :
 NEB_PureFrame.run (Event:=Event) state (NFF_LoggedPush.privatePush NFG_Primitive64.reply self a b)=
 NEB_PureFrame.run state (FIo_Native.fast_pairing.canonical.Dot.push self a b) :=
 NEB_PureFrame.equality state _ _ (NFG_PushComposed.private_result self a b)

theorem public_result_state_effects {State Event : Type} (state : State)
 (self : FIo_Native.fast_pairing.EbyKDot) (value : NE) (scalar : NQ) :
 NEB_PureFrame.run (Event:=Event) state (NFF_LoggedPush.publicPush NFG_Primitive64.reply self value scalar)=
 NEB_PureFrame.run state (FIo_Native.fast_pairing.EbyKDot.push self value scalar) :=
 NEB_PureFrame.equality state _ _ (NFG_PushComposed.public_result self value scalar)

/-- All tail domains and all three whole-receiver overwrite relations come
from the SAME accepted root, after the primitive-native/model association. -/
theorem accepted_packet (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
 (canonical : NEV_DotInputs.Canonical g) (slot : Usize) (out : NE)
 (accepted : NFG_FullDot.one q g slot=ok out) :
 ∃ packet : NFE_NFC_MainPacket.Packet q g slot out,
 NFE_WrapperBridge.NativeDomains packet ∧
 NFE_NFC_ReceiverModel.overwrite packet.tailPacket.state0
  (NFE_NFC_ReceiverModel.words packet.tailPacket.state1)=packet.tailPacket.state1 ∧
 NFE_NFC_ReceiverModel.overwrite packet.tailPacket.state1
  (NFE_NFC_ReceiverModel.words packet.tailPacket.state2)=packet.tailPacket.state2 ∧
 NFE_NFC_ReceiverModel.overwrite packet.tailPacket.state2
  (NFE_NFC_ReceiverModel.words packet.tailPacket.state3)=packet.tailPacket.state3 := by
 rw [NFG_FullDot.one_result q g canonical slot] at accepted
 obtain ⟨packet⟩ := NFE_NFC_MainPacket.of_run q g slot out accepted
 obtain ⟨first,second,third⟩ := NFE_NFC_StepAssociation.packet packet.tailPacket
 exact ⟨packet,NFE_WrapperBridge.domains packet canonical,first,second,third⟩
#print axioms one_result_state_effects
#print axioms four_result_state_effects
#print axioms private_result_state_effects
#print axioms public_result_state_effects
#print axioms accepted_packet
end AspisR1.NFG_DotComposed
end
