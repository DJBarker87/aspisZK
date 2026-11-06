import S2W_D189Entry
import NLE_Length
set_option autoImplicit false
noncomputable section
namespace NLE_SnapshotClause
open Aeneas Aeneas.Std Result AspisR1.S2W_D189Entry
/-- Local snapshot clause, derived from the computed SAME runtime input.
This is not a new premise of a positive parent root. -/
theorem proof_bytes (entry : Entry) (bytes : Slice U8)
 (read : (entry.snapshot 0 58295 58295).bytes = .Ok bytes) :
 bytes.val.length = 58295 := by
 unfold Entry.snapshot at read
 dsimp only at read
 split at read
 · rename_i allowed
   cases read
   exact allowed.elim id id
 · cases read
/-- The C01 extent follows at the entered child site from the SAME snapshot
bytes and the caller's checked-range length guard. -/
theorem proof_scope (entry : Entry) (bytes : Slice U8) (proofEnd : Nat)
 (read : (entry.snapshot 0 58295 58295).bytes = .Ok bytes)
 (guard : bytes.val.length = proofEnd) : proofEnd - 688 = 57607 :=
 NLE_Length.proof_extent bytes.val.length proofEnd (proof_bytes entry bytes read) guard
#print proof_bytes
#print proof_scope
#print axioms proof_bytes
#print axioms proof_scope
end NLE_SnapshotClause
