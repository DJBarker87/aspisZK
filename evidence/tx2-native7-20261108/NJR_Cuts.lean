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
inserted beyond the harness's four word comparisons. 
Native source: NJR_parent.rs.txt, sha256 8cbf394e884584117bc5ec545546723403ab9a8ca81fe9d5a1b26f67a5295ca1, harness pending_destination.
Assertion transcription: `assert_eq!(observed,ptr.wrapping_add(i) as *mut [u64;4]);
assert_eq!(index,i+1);assert_eq!(raw.len(),64);assert_eq!(raw.capacity(),cap);assert_eq!(raw.as_ptr(),ptr);
assert_eq!(raw[j][0],expected[0]);assert_eq!(raw[j][1],expected[1]);assert_eq!(raw[j][2],expected[2]);assert_eq!(raw[j][3],expected[3]);`
Native ownership/capacity facts stay in the certificate packet; no additional
model field, child success or endpoint equation is inferred here.
-/
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
It starts at the return boundary and does not assert unobserved call arguments. 
Native source: NJR_parent.rs.txt, sha256 8cbf394e884584117bc5ec545546723403ab9a8ca81fe9d5a1b26f67a5295ca1, harness query_weights/query_raw/query_scalars.
Assertion transcription: `assert_eq!(log.calls,1);assert!(log.reply.is_none());
match result{Err(e)=>assert_eq!(Some(e),err),Ok((weights,out_rhs,out_power,out_next,pending))=>{
assert!(err.is_none());
if C==0{assert_eq!(weights.as_ptr(),wp);assert_eq!(weights.len(),64);assert_eq!(weights.capacity(),wc);let mut expected=before[i];if cfg!(NJR_invert){expected[0]^=1;}assert_eq!(kw(weights[i]),expected);}
if C==1{assert_eq!(pending.raw.as_ptr(),rp);assert_eq!(pending.raw.len(),64);assert_eq!(pending.raw.capacity(),rc);let mut expected=rows[i];if cfg!(NJR_invert){expected[0]^=1;}assert_eq!(pending.raw[i],expected);}
if C==2{let mut expected=rhs.to_limbs();if cfg!(NJR_invert){expected[0]^=1;}assert_eq!(out_rhs.to_limbs(),expected);assert_eq!(out_power,power);assert_eq!(out_next,next);assert_eq!(pending.terms,terms);}`
Native ownership/capacity facts stay in the certificate packet; no additional
model field, child success or endpoint equation is inferred here.
-/
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
canonical in this definition. 
Native source: NJR_parent.rs.txt, sha256 8cbf394e884584117bc5ec545546723403ab9a8ca81fe9d5a1b26f67a5295ca1, harness flush_receiver_window + flush_destination_window.
Assertion transcription: `let w=&mut slot;assert_eq!(w as *mut K,slot_ptr);
assert_eq!(log.calls,1);assert_eq!(log.index,index);let seen=log.seen.unwrap();assert_eq!(seen as *const BatchedWeights,bp);assert_eq!(seen.terms,terms);assert_eq!(seen.raw.as_ptr(),rp);assert_eq!(seen.raw.capacity(),cap);assert_eq!(seen.raw.len(),64);assert_eq!(seen.raw[j],rows[j]);
let mut expected=kw(reply);if cfg!(NJR_invert){expected[0]^=1;}assert_eq!(kw(slot),expected);
assert_eq!(index,i);assert_eq!(destination,ptr.wrapping_add(i^(if cfg!(NJR_bad_destination){1}else{0})) as *mut K);
assert_eq!(weights.as_ptr(),ptr);assert_eq!(weights.capacity(),cap);assert_eq!(weights.len(),64);
let mut expected=if i==j{kw(reply)}else{before[j]};if cfg!(NJR_invert){expected[0]^=1;}assert_eq!(kw(weights[j]),expected);`
Native ownership/capacity facts stay in the certificate packet; no additional
model field, child success or endpoint equation is inferred here.
-/
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
