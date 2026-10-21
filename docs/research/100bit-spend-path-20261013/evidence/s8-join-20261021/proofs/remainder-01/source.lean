import S8JoinCompactTotal

/-! Retain the concrete reason a length-blind scan/canonical equality is false. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S8JoinScanRemainder
open Aeneas Aeneas.Std Result
open OraclePortCompactDraft S8JoinCompactChunks S8JoinCompactTotal

theorem short_scan (bytes : Slice U8) (short : bytes.val.length<16) :
    S8OwnedP6.check_values_owned bytes=.ok (.Ok ()) := by
  rw [check_values_total]
  have div : (wire bytes).length/16=0 := by simp only [wire,List.length_map]; omega
  simp [scanResult,consumed,div,canonical,slice]

/-- Rust ignores a four-byte noncanonical tail; the frozen canonical word
predicate rejects it. Actual y1 has 464 bytes, so this case is unreachable there. -/
theorem unaligned_mismatch : ∃ bytes : Slice U8,
    S8OwnedP6.check_values_owned bytes=.ok (.Ok ()) ∧ ¬canonical (wire bytes) := by
  let bytes : Slice U8 := ⟨[255#u8,255#u8,255#u8,255#u8],by simp; scalar_tac⟩
  refine ⟨bytes,short_scan bytes (by simp [bytes]),?_⟩
  simp [bytes,wire,canonical,slice,little,AspisV8R19.SqueezeOracleBridge.decodeByte]

#print axioms short_scan
#print axioms unaligned_mismatch
end AspisR1.S8JoinScanRemainder
end
