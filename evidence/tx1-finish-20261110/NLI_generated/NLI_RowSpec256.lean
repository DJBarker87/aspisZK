import NLC_Step_terminal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_TerminalInterface
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
abbrev Public := pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Challenges := r1_wire.Challenges
abbrev Reply := Result (core.result.Result Q aspis_core.state_only_prefix.r0.Error)
/-- Complete interpreted borrow frame, including arbitrary caller-owned rest
heap. A native producer must realize the frozen function on this carrier;
this record alone is not a physical-memory interpretation. -/
structure Observation (A : Type) where
 publicAfter : Public
 claimsAfter : Claims
 alphaAfter : Alpha
 challengesAfter : Challenges
 heapAfter : A
 reply : Reply
 effects : PreparedHashCode.Log
abbrev Native := ∀ A : Type,A → Public → Claims → Alpha → Challenges → Observation A
/-- Proposed typed child256 obligation under(be)(1), pending ledger review.
No successful reply or independently chosen endpoint is a premise. Heap
includes the caller's owner/allocator state; all borrows are preserved. The
frozen native producer and physical interpretation must be fixed by NLH.
No runtime/digest action is added: the adopted terminal boundary is pure.
Internal arithmetic/canonicality and error/abort coverage remain in this full
Result equality, not a stronger caller precondition. -/
def RowSpec_256 (native : Native) : Prop :=
 ∀ (A : Type) (heap : A) (publicValue : Public) (claims : Claims)
 (alpha : Alpha) (challenges : Challenges),
 let observed := native A heap publicValue claims alpha challenges
 observed.publicAfter=publicValue ∧ observed.claimsAfter=claims ∧
 observed.alphaAfter=alpha ∧ observed.challengesAfter=challenges ∧
 observed.heapAfter=heap ∧ observed.effects=[] ∧
 observed.reply=FIq_Terminal.terminal publicValue claims alpha challenges
#print RowSpec_256
end AspisR1.NLI_TerminalInterface
end
