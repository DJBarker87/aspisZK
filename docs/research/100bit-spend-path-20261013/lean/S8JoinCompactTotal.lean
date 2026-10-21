import S8JoinCompactChunks

/-! Full-Result scan refinement, including noncanonical rejection and the
ignored partial trailing chunk. No length or canonicality precondition. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S8JoinCompactTotal
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open Aeneas Aeneas.Std Result
open OraclePortCompactDraft S8JoinCompactChunks
open S8OwnedP6 S8OwnedP6Scan
attribute [local instance] Classical.propDecidable

/-- Exactly the prefix consumed by Rust chunks_exact(16). -/
def consumed (b : Bytes) : Bytes := b.take (16*(b.length/16))

def scanResult (b : Bytes) : Status :=
  if canonical (consumed b) then .Ok () else .Err .NonCanonical

theorem consumed_length (b : Bytes) : (consumed b).length = 16*(b.length/16) := by
  simp only [consumed,List.length_take]
  exact Nat.min_eq_left (by omega)

theorem consumed_slice (b : Bytes) (j : Nat) (hj : j < b.length/16) :
    slice (consumed b) (16*j) 16 = slice b (16*j) 16 := by
  change slice (slice b 0 (16*(b.length/16))) (16*j) 16 = _
  simpa only [Nat.zero_add] using
    slice_slice b 0 (16*(b.length/16)) (16*j) 16 (by omega)

theorem consumed_chunks (b : Bytes) : canonical (consumed b) ↔
    ∀ j, j < b.length/16 → canonical (slice b (16*j) 16) := by
  rw [canonical_chunks _ (by rw [consumed_length]; omega)]
  simp only [consumed_length,Nat.mul_div_cancel_left _ (by decide : 0<16)]
  constructor
  · intro h j hj
    simpa only [consumed_slice b j hj] using h j hj
  · intro h j hj
    simpa only [consumed_slice b j hj] using h j hj

/-- Total equality for every byte slice: the inner codec Err is preserved,
while no panic/divergence or successful-parser premise is introduced. -/
theorem check_values_total (bytes : Slice U8) :
    check_values_owned bytes = .ok (scanResult (wire bytes)) := by
  obtain ⟨out,run,accepted,branches⟩ := S8OwnedP6StrictScanModel.strict_scan_total bytes
  have good : out = .Ok () ↔ canonical (consumed (wire bytes)) := by
    rw [consumed_chunks]
    simp only [wire,List.length_map]
    exact accepted.trans ⟨fun h j hj => (chunk_iff bytes j hj).mp (h j hj),
      fun h j hj => (chunk_iff bytes j hj).mpr (h j hj)⟩
  unfold scanResult
  split
  · rename_i hc
    simpa only [(good.mpr hc)] using run
  · rename_i hc
    have he : out = .Err .NonCanonical := by
      rcases branches with success | rejected
      · exact False.elim (hc (good.mp success))
      · exact rejected
    simpa only [he] using run

/-- At actual aligned call sites no bytes are discarded. -/
theorem aligned_scan_total (bytes : Slice U8) (multiple : bytes.val.length%16=0) :
    check_values_owned bytes = .ok
      (if canonical (wire bytes) then .Ok () else .Err .NonCanonical) := by
  have hlen : (wire bytes).length%16=0 := by simpa [wire] using multiple
  have same : consumed (wire bytes) = wire bytes := by
    unfold consumed
    have size : 16*((wire bytes).length/16) = (wire bytes).length := by omega
    rw [size,List.take_length]
  simpa only [scanResult,same] using check_values_total bytes

#print axioms consumed_length
#print axioms consumed_slice
#print axioms consumed_chunks
#print axioms check_values_total
#print axioms aligned_scan_total
end AspisR1.S8JoinCompactTotal
end
