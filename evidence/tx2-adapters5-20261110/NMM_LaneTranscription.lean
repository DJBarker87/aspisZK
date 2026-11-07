import NLK_LaneInvocation
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace NMM_LaneTranscription
open Aeneas Aeneas.Std Result AspisR1 NKP_LaneCuts
abbrev Lane := NLA_LaneAssemble.Lane
abbrev PE := NKF_BoxModel.PE

/-- Literal source order: extent/header/master/tree/sequence, root decoder,
20 frontier iterations with first-error return, terminal empty-root check,
then the sole owned Box allocation. Child definitions are already CLOSED.
Native-to-transcription correspondence is a separate, still open obligation. -/
def value (bytes : Slice U8) : Result (core.result.Result Lane PE) := do
 if h : bytes.val.length = 768 then
  let p : NLK_LaneInput.Sized := ⟨bytes, h⟩
  match NLK_LaneHeader.sourcePrefix p with
  | .Err error => ok (.Err error)
  | .Ok fields =>
   let decoded ← NLK_LaneDigest.source (NLK_LaneInput.root p)
   match decoded with
   | .Err _ => ok (.Err .InvalidAccountData)
   | .Ok root =>
    let frontier ← NLK_LaneLoopSource.run p fields.next
      NLK_LaneLoop.levels NLK_LaneLoop.zero
    ok (NKP_LaneCompletion.finish fields.bump fields.master fields.lane
      fields.next root NLK_LaneTable.final frontier).1
 else ok (.Err .InvalidAccountData)

theorem adopted_value (bytes : Slice U8) :
 value bytes = NLK_LaneProgram.reference bytes := by rfl

def owned {S : Type} (allocator : S2W_D189Wrappers.Allocator S)
 (before : S) (reservation : NP6_StdModel.Reservation) (owner : Nat)
 (bytes : Slice U8) :=
 NKY_BoxAction.run allocator before 720 reservation owner (value bytes)

/-- All allocator Result arms and the 720-byte request are retained. This is a
model theorem, not a native row root; allocator success is never presumed. -/
theorem adopted_owned {S : Type} (allocator : S2W_D189Wrappers.Allocator S)
 (before : S) (reservation : NP6_StdModel.Reservation) (owner : Nat)
 (bytes : Slice U8) :
 owned allocator before reservation owner bytes =
 NLK_LaneProgram.owned allocator before reservation owner bytes := by rfl

theorem complete_value (bytes : Slice U8) :
 value bytes = ok (NLK_LaneProgram.referenceValue bytes) := by
 rw [adopted_value, NLK_LaneProgram.source]

#print adopted_value
#print axioms adopted_value
#print adopted_owned
#print axioms adopted_owned
#print complete_value
#print axioms complete_value
end NMM_LaneTranscription
