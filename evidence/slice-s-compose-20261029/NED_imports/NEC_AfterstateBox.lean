import NEC_Reference.Funs
import AspisR1TerminalDecoder.Funs
set_option autoImplicit false
namespace NEC_AfterstateBox
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder
abbrev Value := pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev ChildError := pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
abbrev Error := pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1

def PacketDomain (bytes : Slice U8) : Prop := bytes.val.length=688

def reference (reply : core.result.Result Value ChildError) :
 Result (core.result.Result Value Error) := do
 let raw ← NEC_Reference.boxed_ref reply
 match raw with
 | .Ok value => ok (.Ok value)
 | .Err (.Child error) => ok (.Err (.Afterstate error))

/-- Exact emitted wrapper over the SAME child Result, including all child errors.
The child decoder's own native bridge is separate and must be instantiated. -/
theorem emitted (bytes : Slice U8) (reply : core.result.Result Value ChildError)
 (child : pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes=ok reply) :
 pool_v1.pair_tree_profile.decode_pair_afterstate_boxed_v1 bytes=reference reply := by
 unfold pool_v1.pair_tree_profile.decode_pair_afterstate_boxed_v1
 rw [child]
 cases reply <;> rfl

/-- The native selected-word observation is valid for every projection, so
finite record assembly does not strengthen the input domain. -/
theorem value_project (reply : core.result.Result Value ChildError) (value : Value)
 (returned : reference reply=ok (.Ok value)) : reply=.Ok value := by
 cases reply <;> simp_all [reference,NEC_Reference.boxed_ref]

#print axioms emitted
#print axioms value_project
end NEC_AfterstateBox
