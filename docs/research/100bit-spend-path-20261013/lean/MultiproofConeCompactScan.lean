import MultiproofConeQMScan
import MultiproofConeRead16
import MultiproofConeCanonicalAppend

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeCompactScan
open Aeneas Aeneas.Std Result
open OraclePortCompactDraft
open MultiproofConeCanonical MultiproofConeCanonicalAppend
attribute [local instance] Classical.propDecidable

theorem check_values_total (bytes : Slice U8) (aligned : bytes.val.length % 16 = 0) :
    MultiproofParserRef.reference.check_values bytes =
      ok (decide (canonical (bytesOf bytes.val))) := by
  generalize hn : bytes.val.length = n
  induction n using Nat.strong_induction_on generalizing bytes with
  | h n ih =>
    rw [MultiproofParserRef.reference.check_values]
    by_cases short : Slice.len bytes < 16#usize
    · simp only [short, if_true]
      have small : bytes.val.length < 16 := short
      have zero : bytes.val.length = 0 := by omega
      have empty := List.eq_nil_of_length_eq_zero zero
      simp [empty, bytesOf, canonical]
    · simp only [short, if_false]
      have bound : 16 ≤ bytes.val.length := by
        change ¬ bytes.val.length < 16 at short
        omega
      obtain ⟨chunk,hread,hval⟩ := MultiproofConeRead16.read16_total bytes bound
      rw [hread]
      simp only [bind_tc_ok, MultiproofConeQMScan.qm_total, decide_eq_true_eq]
      let rest : Slice U8 := Slice.drop bytes 16#usize
      have restLength : rest.val.length = bytes.val.length - 16 := by
        simp only [rest, Slice.getElem!_val_drop, List.length_drop,
          show (16#usize).val = 16 from rfl]
      have restAligned : rest.val.length % 16 = 0 := by rw [restLength]; omega
      have restSmaller : rest.val.length < n := by rw [restLength]; omega
      have ht := ih rest.val.length restSmaller rest restAligned rfl
      have chunkBytes : bytesOf chunk.val = (bytesOf bytes.val).take 16 := by
        rw [hval]
        simp only [bytesOf, List.map_take]
      have restBytes : bytesOf rest.val = (bytesOf bytes.val).drop 16 := by
        simp only [rest, Slice.getElem!_val_drop, bytesOf, List.map_drop,
          show (16#usize).val = 16 from rfl]
      have parts := canonical_take_drop (bytesOf bytes.val) 16 (by decide)
        (by simpa only [bytesOf,List.length_map] using bound)
      by_cases hc : canonical (bytesOf chunk.val)
      · simp only [hc, if_true]
        simp only [core.slice.index.Slice.index,
          core.slice.index.SliceIndexRangeFromUsizeSlice.index,
          show (16#usize).val = 16 from rfl,
          show 16 ≤ bytes.length from bound, if_true, bind_tc_ok]
        change MultiproofParserRef.reference.check_values rest = _
        rw [ht]
        have equiv : canonical (bytesOf bytes.val) ↔ canonical (bytesOf rest.val) := by
          rw [parts, ← chunkBytes, ← restBytes]
          simp only [hc, true_and]
        rw [propext equiv]
      · simp only [hc, if_false]
        have bad : ¬ canonical (bytesOf bytes.val) := by
          intro hfull
          exact hc (by rw [chunkBytes]; exact (parts.mp hfull).1)
        simp only [bad, decide_false]

#print axioms check_values_total
end AspisR1.MultiproofConeCompactScan
end
