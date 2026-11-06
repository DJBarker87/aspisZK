import NLE_RangeClause
import NLE_SafeCuts
set_option autoImplicit false
noncomputable section
namespace NLE_CallerScope
open Aeneas Aeneas.Std Result AspisR1.S2W_D189Entry
/-- The SAME checkpoint snapshot's deferred length branch supplies its extent. -/
theorem checkpoint (entry : Entry) (bytes : Slice U8)
 (read : (entry.snapshot 6 1768 1768).bytes = .Ok bytes) : bytes.val.length = 1768 := by
 unfold Entry.snapshot at read
 dsimp only at read
 split at read
 · rename_i allowed
   cases read
   exact allowed.elim id id
 · cases read
/-- Only numeric metadata is formed here: addresses carry no payload identity. -/
def metadata (publicAddress proofAddress checkpointAddress : Nat)
 (publicBytes proof checkpoint : Slice U8) : NLE_SafeCuts.State :=
 ⟨⟨publicAddress,publicBytes.val.length⟩,⟨proofAddress,proof.val.length⟩,
  ⟨checkpointAddress,checkpoint.val.length⟩⟩
/-- Every fixed-extent clause of the safe native segment is derived from the
SAME local reads/range and encoder carrier. No free size hypothesis. -/
theorem scope (entry : Entry) (proofAccount proof checkpointBytes : Slice U8)
 (publicBytes : Array U8 1880#usize) (proofEnd : Usize)
 (publicAddress proofAddress checkpointAddress : Nat)
 (proofRead : (entry.snapshot 0 58295 58295).bytes = .Ok proofAccount)
 (checkpointRead : (entry.snapshot 6 1768 1768).bytes = .Ok checkpointBytes)
 (guard : proofAccount.val.length = proofEnd.val)
 (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   proofAccount {start := 688#usize, «end» := proofEnd} = ok proof) :
 NLE_SafeCuts.Scope (metadata publicAddress proofAddress checkpointAddress publicBytes.to_slice proof checkpointBytes) := by
 have exactProof := (NLE_RangeClause.caller_proof entry proofAccount proof proofEnd proofRead guard range).1
 exact ⟨NLE_Length.public_extent publicBytes,exactProof,checkpoint entry checkpointBytes checkpointRead⟩
#print checkpoint
#print scope
#print axioms checkpoint
#print axioms scope
end NLE_CallerScope
