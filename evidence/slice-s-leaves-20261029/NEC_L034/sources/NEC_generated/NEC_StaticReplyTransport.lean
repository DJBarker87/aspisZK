import NEC_AfterstateWindows
import NEC_PureReplyAssociation
set_option autoImplicit false
namespace NEC_StaticReplyTransport
open Aeneas Aeneas.Std Result
open NEC_AfterstateBox

/-- The successful native callbacks return one immutable arbitrary whole reply.
Each projection window therefore quantifies over the same reply record. The
native semantic transport premise is explicit; no mutable monitor is assumed. -/
def Packet (reply : core.result.Result Value ChildError)
 (actual : core.result.Result Value Error) : Prop :=
 match reply with
 | .Ok expected=>∃ returned, actual=.Ok returned ∧ NEC_AfterstateWindows.Fields returned expected
 | .Err error=>actual=.Err (.Afterstate error)

theorem transport (reply : core.result.Result Value ChildError)
 (actual : core.result.Result Value Error) (packet : Packet reply actual) :
 ok actual=reference reply := by
 cases reply with
 | Ok expected=>
   obtain ⟨returned,same,fields⟩ := packet
   have values := NEC_AfterstateWindows.assemble returned expected fields
   subst returned
   rw [same]
   rfl
 | Err error=>
   change actual=.Err (.Afterstate error) at packet
   rw [packet]
   rfl

theorem emitted_transport (bytes : Slice U8)
 (reply : core.result.Result Value ChildError)
 (actual : core.result.Result Value Error)
 (child : AspisR1TerminalDecoder.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes=ok reply)
 (packet : Packet reply actual) :
 AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pair_afterstate_boxed_v1 bytes=ok actual := by
 rw [NEC_AfterstateBox.emitted bytes reply child]
 exact (transport reply actual packet).symm

#print axioms transport
#print axioms emitted_transport
end NEC_StaticReplyTransport
