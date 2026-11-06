import NLE_SnapshotClause
import AdapterRwRanges
set_option autoImplicit false
noncomputable section
namespace NLE_RangeClause
open Aeneas Aeneas.Std Result AspisR1.S2W_D189Entry
/-- Entered caller range from the SAME computed snapshot: exact byte suffix
and C01 length. Conditions are local cut observations, never root premises. -/
theorem caller_proof (entry : Entry) (bytes selected : Slice U8) (proofEnd : Usize)
 (read : (entry.snapshot 0 58295 58295).bytes = .Ok bytes)
 (guard : bytes.val.length = proofEnd.val)
 (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   bytes {start := 688#usize, «end» := proofEnd} = ok selected) :
 selected.val.length = 57607 ∧ bytes.val = bytes.val.take 688 ++ selected.val := by
 have size := NLE_SnapshotClause.proof_bytes entry bytes read
 have ordered : (688#usize).val ≤ proofEnd.val := by change 688 ≤ proofEnd.val; omega
 have facts := AspisR1.AdapterRw.Ranges.suffix_exact bytes selected 688#usize proofEnd ordered guard range
 refine ⟨?_,facts.2⟩
 rw [facts.1]
 change proofEnd.val - 688 = 57607
 omega
#print caller_proof
#print axioms caller_proof
end NLE_RangeClause
