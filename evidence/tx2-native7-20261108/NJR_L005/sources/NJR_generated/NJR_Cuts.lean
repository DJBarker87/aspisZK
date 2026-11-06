import NJJ_Cuts
import NJJ_Flush
set_option autoImplicit false
noncomputable section
namespace NJR_Cuts
open Aeneas Aeneas.Std Result AspisR1
abbrev K := VTop_Stages.aspis_core.field.QM31
abbrev Row := Port3_NativePendingBody.Row

/-- Logical payload of pending_destination (NJR_parent.rs). Pointer/capacity
facts are native ownership observations, retained in the certificate table.
The arbitrary observation j covers the full post-state. No extra frame is
inserted beyond the harness's four word comparisons. -/
def pending (weights : Slice K) (before after : alloc.vec.Vec Row)
 (index next : Nat) : Prop := NJJ_Cuts.pendingStep weights before after index next

theorem pending_store (weights : Slice K) (before after : alloc.vec.Vec Row)
 (i next : Nat) (w : K) (read : weights.val[i]?=some w)
 (size : before.val.length=64) (inside : i<64)
 (cut : pending weights before after i next) :
 after.val=before.val.set i (Port3_PendingInstall.row w) :=
 NJJ_Cuts.pending_payload weights before after i next w read size inside cut

/-- Full logical query-return footprint asserted by the three supplementary
native windows. Error is the exact child error; the complete record is moved.
It starts at the return boundary and does not assert unobserved call arguments. -/
def queryReturn (reply : core.result.Result
 (VTop_Stages.verifier.Accumulator × VTop_Stages.verifier.BatchedWeights)
 VTop_Stages.verifier.Error)
 (post : core.result.Result
 (alloc.vec.Vec K × VTop_Stages.aspis_core.field.wide_exact.WideExact × K × Usize ×
 VTop_Stages.verifier.BatchedWeights) VTop_Stages.verifier.Error) : Prop :=
 post = match reply with
 | .Err e => .Err e
 | .Ok (a,b) => .Ok (a.weights,a.rhs,a.power,a.next,b)

/-- Match the full moved query carrier to the frozen destructuring, including
all raw/weights cells, lengths and scalar fields (not an address-to-value law). -/
theorem query_reconstruct
 (a : VTop_Stages.verifier.Accumulator) (b : VTop_Stages.verifier.BatchedWeights)
 (weights : alloc.vec.Vec K)
 (rhs : VTop_Stages.aspis_core.field.wide_exact.WideExact) (power : K) (next : Usize)
 (pending : VTop_Stages.verifier.BatchedWeights)
 (cut : queryReturn (.Ok (a,b)) (.Ok (weights,rhs,power,next,pending))) :
 ({weights,rhs,power,next} : VTop_Stages.verifier.Accumulator)=a ∧ pending=b := by
 have same : (weights,rhs,power,next,pending)=(a.weights,a.rhs,a.power,a.next,b) :=
  core.result.Result.Ok.inj cut
 cases same
 cases a
 exact ⟨rfl,rfl⟩

/-- SAME immutable raw receiver/index and arbitrary full K reply. The output
frame is pointwise, so finite iteration composes without native whole-buffer
execution. The reply is instantiated by the CLOSED value law, not assumed
canonical in this definition. -/
def flushStep (raw beforeRaw : List Row) (terms beforeTerms : Usize)
 (before after : List K) (index : Nat) (reply : K) : Prop :=
 raw=beforeRaw ∧ terms=beforeTerms ∧ after.length=before.length ∧
 ∀ j, j<before.length → after[j]?=if index=j then some reply else before[j]?

theorem flush_store (raw beforeRaw : List Row) (terms beforeTerms : Usize)
 (before after : List K) (i : Nat) (reply : K) (inside : i<before.length)
 (cut : flushStep raw beforeRaw terms beforeTerms before after i reply) :
 after=before.set i reply := by
 have length := cut.2.2.1
 apply List.ext_getElem?
 intro j
 by_cases hj : j<before.length
 · rw [cut.2.2.2 j hj]
   by_cases same : i=j
   · subst j
     rw [if_pos rfl,List.getElem?_set_self inside]
   · rw [if_neg same,List.getElem?_set_ne same]
 · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by simpa only [List.length_set] using Nat.le_of_not_gt hj)]

#print axioms pending_store
#print axioms query_reconstruct
#print axioms flush_store
end NJR_Cuts
