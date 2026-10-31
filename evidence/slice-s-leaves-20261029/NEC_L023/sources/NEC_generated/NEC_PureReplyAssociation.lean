import NEC_ReplyRef.Funs
import NEC_AfterstateBox
set_option autoImplicit false
namespace NEC_PureReplyAssociation
open Aeneas Aeneas.Std Result
open NEC_AfterstateBox

def pure (reply : core.result.Result Value ChildError) : Result (core.result.Result Value Error) := do
 let raw ← NEC_ReplyRef.reply_ref reply
 match raw with
 | .Ok value => ok (.Ok value)
 | .Err (.Child error) => ok (.Err (.Afterstate error))

/-- Aeneas erases the library Box allocation. This equality does not establish
native allocation or mutable-observer correctness (K010/K017 remain findings). -/
theorem reference_equality (reply : core.result.Result Value ChildError) :
 reference reply=pure reply := by
 cases reply <;> rfl

theorem emitted (bytes : Slice U8) (reply : core.result.Result Value ChildError)
 (child : AspisR1TerminalDecoder.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes=ok reply) :
 AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pair_afterstate_boxed_v1 bytes=pure reply := by
 rw [NEC_AfterstateBox.emitted bytes reply child,reference_equality]

/-- The native envelope includes every actual afterstate caller (length688),
including arbitrary bytes that the child decoder rejects. -/
def PacketDomain (bytes : Slice U8) : Prop := bytes.val.length≤688

theorem caller_domain (bytes : Slice U8) (length : bytes.val.length=688) : PacketDomain bytes := by
 unfold PacketDomain
 omega

#print axioms reference_equality
#print axioms emitted
#print axioms caller_domain
end NEC_PureReplyAssociation
