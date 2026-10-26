import PFin_AddressBound
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_LeafBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortSelectedDraft

theorem slice_bound (b : Bytes) (offset count : Nat) : (slice b offset count).length≤count := by
  exact List.length_take_le count (b.drop offset)

theorem leaf (p : Parsed) (kind pos : Nat) : (OraclePortSelectedDraft.leaf p kind pos).length≤514 := by
  have packed0 := List.length_take_le 480 (opening p pos)
  have packed1 := slice_bound (opening p pos) 480 128
  have packed2 := slice_bound (opening p pos) 672 128
  have salt0 := slice_bound (opening p pos) 608 32
  have salt1 := slice_bound (opening p pos) 640 32
  have salt2 := slice_bound (opening p pos) 800 32
  unfold OraclePortSelectedDraft.leaf
  split_ifs <;> simp only [BinMerkle32Leaf.leafInput,List.length_cons,List.length_append] <;> omega

#print axioms slice_bound
#print axioms leaf
end AspisR1.PFin_LeafBound
end
