import NLK_LaneLoopSource
import NLK_LaneSuffixLaw
import NLK_ProgramBorrowScope
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace NLK_LaneProgram
open Aeneas Aeneas.Std Result AspisR1
open NKP_LaneCuts
abbrev Lane := NLA_LaneAssemble.Lane
abbrev PE := NKF_BoxModel.PE
abbrev Sized := NLK_LaneInput.Sized

def body (p : Sized) : core.result.Result Lane PE :=
 match NLK_LaneHeader.sourcePrefix p with
 | .Err e => .Err e
 | .Ok f =>
  match NLK_LaneDigest.decode (NLK_LaneInput.root p) with
  | .Err _ => .Err .InvalidAccountData
  | .Ok root =>
   (NKP_LaneCompletion.finish f.bump f.master f.lane f.next root NLK_LaneTable.final
    (NKF_LaneTrace.run NLK_LaneTable.empty (NLK_LaneLoop.occupied f.next)
      (NLK_LaneLoop.raw p) NLK_LaneLoop.levels NLK_LaneLoop.zero)).1

/-- Literal value-stage order with the CLOSED emitted root decoder at the SAME
original bytes and one canonical native-window step per loop occurrence.
This is a mathematical source interpretation, not a native-row promotion. -/
def sourceSized (p : Sized) : Result (core.result.Result Lane PE) := do
 match NLK_LaneHeader.sourcePrefix p with
 | .Err e => ok (.Err e)
 | .Ok f =>
  let raw ← NLK_LaneDigest.source (NLK_LaneInput.root p)
  match raw with
  | .Err _ => ok (.Err .InvalidAccountData)
  | .Ok root => do
   let loop ← NLK_LaneLoopSource.run p f.next NLK_LaneLoop.levels NLK_LaneLoop.zero
   ok (NKP_LaneCompletion.finish f.bump f.master f.lane f.next root NLK_LaneTable.final loop).1

theorem source_sized (p : Sized) : sourceSized p=ok (body p) := by
 unfold sourceSized body
 cases h : NLK_LaneHeader.sourcePrefix p with
 | Err e => rfl
 | Ok f =>
  rw [NLK_LaneDigest.child]
  simp only [bind_tc_ok]
  cases r : NLK_LaneDigest.decode (NLK_LaneInput.root p) with
  | Err e => rfl
  | Ok root => rw [NLK_LaneLoopSource.source,NLK_LaneLoop.fold];rfl

def referenceValue (bytes : Slice U8) : core.result.Result Lane PE :=
 if h : bytes.val.length=768 then body ⟨bytes,h⟩ else .Err .InvalidAccountData

def reference (bytes : Slice U8) : Result (core.result.Result Lane PE) :=
 if h : bytes.val.length=768 then sourceSized ⟨bytes,h⟩ else ok (.Err .InvalidAccountData)

theorem source (bytes : Slice U8) : reference bytes=ok (referenceValue bytes) := by
 unfold reference referenceValue
 split
 · exact source_sized _
 · rfl

/-- THIS source invocation's sole Box site consumes the reservation, allocator
post, same720-byte request, alignment8 and actual owned carrier. -/
def owned {S : Type} (a : S2W_D189Wrappers.Allocator S) (before : S)
 (r : NP6_StdModel.Reservation) (owner : Nat) (bytes : Slice U8) :=
 NKY_BoxAction.run a before 720 r owner (reference bytes)

theorem allocation {S : Type} (a : S2W_D189Wrappers.Allocator S) (before : S)
 (r : NP6_StdModel.Reservation) (owner : Nat) (bytes : Slice U8) :
 owned a before r owner bytes =
 NKY_BoxAction.run a before 720 r owner (ok (referenceValue bytes)) := by
 unfold owned
 rw [source]

theorem wrong_length {S : Type} (a : S2W_D189Wrappers.Allocator S) (before : S)
 (r : NP6_StdModel.Reservation) (owner : Nat) (bytes : Slice U8)
 (bad : bytes.val.length≠768) :
 owned a before r owner bytes=ok (.Err .InvalidAccountData,before) := by
 rw [allocation]
 simp only [referenceValue,dif_neg bad,NKY_BoxAction.run,bind_tc_ok]

theorem allocation_frame {S : Type} (a : S2W_D189Wrappers.Allocator S) (before : S)
 (r : NP6_StdModel.Reservation) (owner : Nat) (bytes : Slice U8)
 (heap : NKY_BoxFrame.Heap Lane) :
 NKY_BoxPacket.Law a before 720 8 r owner heap (reference bytes) :=
 NKY_BoxPacket.complete a before 720 8 r owner heap (reference bytes)

#print source_sized
#print axioms source_sized
#print source
#print axioms source
#print allocation
#print axioms allocation
#print axioms wrong_length
#print axioms allocation_frame
end NLK_LaneProgram
