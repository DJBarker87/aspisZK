import PV_B3Q_BitCounts
namespace PV_B3Q_PanicGuards
open Aeneas Aeneas.Std
set_option autoImplicit false
/-- Source terminal_qm31's 84-iteration selection from [3][29]. -/
theorem selected_claim_bounds (i : Nat) (guard : i < 84) :
    i / 28 < 3 ∧ i % 28 < 29 := by omega
/-- The array const generic of the source caller fixes both dot lengths. -/
theorem dot_map_lengths {α β γ δ : Type} (rows : List α) (f : α → β)
    (g : α → γ) (h : α → δ) :
    (rows.map f).length = (rows.map g).length ∧
    (rows.map f).length = (rows.map h).length := by
 simp only [List.length_map, and_self]
/-- All qm31_pack_base4 callers in the captured terminal pass four-element
arrays; this proves the source assert and every padded write under its loop. -/
theorem pack4_guard (length i : Nat) (shape : length ≤ 4) (loop : i < length) :
    length ≤ 4 ∧ i < 4 ∧ i < length := by omega
/-- The reverse Horner loops decrement before indexing. -/
theorem reverse_read (i n : Nat) (invariant : i ≤ n) (loop : 0 < i) :
    i - 1 < n := by omega
/-- Copy::Selectors::row uses row>>4 and row&15, i.e. division/remainder.
The bit-operation source correspondence remains a compiler intrinsic item. -/
theorem endpoint_selector_bounds (row : Nat) (bound : row < 1024) :
    row / 16 < 64 ∧ row % 16 < 16 := by omega
/-- The only table-dependent shift in link_weight is by weight_level. -/
theorem weight_bit (bit : Nat) (bound : bit < 2) :
    bit = 0 ∨ bit = 1 := by omega
/-- optimized-terminal's chunk width is formed only in this nonempty loop. -/
theorem batch_count_guard (coordinate finish : Nat) (loop : coordinate < finish) :
    1 ≤ min 4 (finish - coordinate) ∧ min 4 (finish - coordinate) ≤ 4 := by
 omega
/-- The two expand callers are (start,count)=(0,6),(6,4). -/
theorem high_coordinate (coordinate : Nat) (guard : coordinate < 0 + 6) :
    coordinate < 10 := by omega
theorem low_coordinate (coordinate : Nat) (guard : coordinate < 6 + 4) :
    coordinate < 10 := by omega
/-- Generic single-stage doubling, before multiplication by the field value.
This is an index proof, independent of every witness and field word. -/
theorem expand_write_bounds (index len capacity : Nat)
    (guard : index < len) (stage : 2 * len ≤ capacity) :
    index < capacity ∧ 2 * index < capacity ∧ 2 * index + 1 < capacity := by omega
/-- The native nonzero-mask branch suffices for the intrinsic cttz index. -/
theorem mask_read_bound (mask : U16) (guard : mask ≠ 0#u16) :
    (UScalar.cast .Usize (PV_B3Q_BitCounts.word (PV_B3Q_BitCounts.bits mask).ctz)).val < 16 :=
 PV_B3Q_BitCounts.native_cast_index_bound mask guard
#print axioms selected_claim_bounds
#print axioms dot_map_lengths
#print axioms pack4_guard
#print axioms reverse_read
#print axioms endpoint_selector_bounds
#print axioms weight_bit
#print axioms batch_count_guard
#print axioms high_coordinate
#print axioms low_coordinate
#print axioms expand_write_bounds
#print axioms mask_read_bound
end PV_B3Q_PanicGuards
