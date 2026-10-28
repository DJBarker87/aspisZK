import JFz_CanonicalAppend
import PSem_Rows
import RPz8_JFx_NativeBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_RowGeometry
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def wire : Bytes := bytesOf JFx_NativeBytes.proof.val

theorem wire_length : wire.length = 57607 := by
  simp only [wire,bytesOf,List.length_map]
  exact JFx_NativeBytes.proofBytes_length

theorem slice_drop (b : Bytes) (off n total : Nat) :
    (slice b off total).drop n = slice b (off+n) (total-n) := by
  simp only [slice,List.drop_take,List.drop_drop]

theorem slice_take (b : Bytes) (off n total : Nat) (bound : n ≤ total) :
    (slice b off total).take n = slice b off n := by
  simp only [slice,List.take_take,Nat.min_eq_left bound]

theorem slice_slice (b : Bytes) (off total skip n : Nat) (bound : n ≤ total-skip) :
    slice (slice b off total) skip n = slice b (off+skip) n := by
  simp only [slice,List.drop_take,List.drop_drop,List.take_take,Nat.min_eq_left bound]

theorem forward (fuel row : Nat) (b : Bytes) (rs : List Bytes)
    (enough : 5+(if 14 ≤ row then (rowShape row).2/2 else (rowShape row).2) ≤ b.length)
    (header : b.take 5 = ⟨(rowShape row).1%256,Nat.mod_lt _ (by decide)⟩ :: le32 (rowShape row).2)
    (canon : 14 ≤ row → canonical (slice b 5 ((rowShape row).2/2)))
    (tail : semanticRows fuel (row+1)
      (b.drop (5+(if 14 ≤ row then (rowShape row).2/2 else (rowShape row).2))) = some rs) :
    semanticRows (fuel+1) row b = some (PSem_Rows.expandedRow row b :: rs) := by
  by_cases compact : 14 ≤ row
  · simp only [if_pos compact] at enough tail
    have valid := canon compact
    simp [semanticRows,PSem_Rows.expandedRow,compact,valid,header,
      Nat.not_lt.mpr enough,tail]
  · simp only [if_neg compact] at enough tail
    simp [semanticRows,PSem_Rows.expandedRow,compact,header,Nat.not_lt.mpr enough,tail]

#print axioms wire_length
#print axioms slice_drop
#print axioms slice_take
#print axioms slice_slice
#print axioms forward
end AspisR1.JFz_RowGeometry
end
