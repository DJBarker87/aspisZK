import S1FirstErrorPartitionV1
set_option autoImplicit false
namespace AspisS1FirstErrorPartition

/-- Exact source expression in weights::field: [column*32,(column+1)*32).
The fixed 928-byte input admits every reached source field frame. Numeric
canonical decoding and native abort behavior are separate obligations. -/
theorem field_frame (column : Nat) (bound : column<29) :
    column+1≤29 ∧ column*32<(column+1)*32 ∧ (column+1)*32≤928 ∧
    column*32+32=(column+1)*32 ∧ 145+column<174 := by omega

/-- All controller/frame indices fit even a 16-bit usize, hence the frozen
64-bit source expressions cannot wrap on the covered point/column domain. -/
theorem source_small_indices (point column : Nat) (p : point<6) (c : column<29) :
    point+1<65535 ∧ column+1<65535 ∧ 29*point+column+1<65535 ∧
    column*32<65535 ∧ (column+1)*32<65535 := by omega

#print axioms field_frame
#print axioms source_small_indices
end AspisS1FirstErrorPartition
