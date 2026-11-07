import NCV_ZeroStep
import NMX_R3_ByteCarrier
set_option autoImplicit false
namespace NMX_R3_Slices
open Aeneas Aeneas.Std Result NMX_R3_ByteCarrier

def window (b : Slice U8) (s n : Nat) : Slice U8 :=
 ⟨(b.val.drop s).take n, by
  have bound := b.property
  simp only [List.length_take, List.length_drop]
  omega⟩

theorem length (b : Slice U8) (s n : Nat) (fit : s+n ≤ b.val.length) :
 (window b s n).val.length = n := by
 simp only [window, List.length_take, List.length_drop]
 omega

theorem range_total (b : Slice U8) (s e : Usize)
 (order : s.val ≤ e.val) (bound : e.val ≤ b.val.length) :
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  b {start:=s, «end»:=e} = ok (window b s.val (e.val-s.val)) := by
 have valid : s ≤ e ∧ e.val ≤ b.length := ⟨order,bound⟩
 simp only [core.slice.index.Slice.index,
  core.slice.index.SliceIndexRangeUsizeSlice.index, valid, if_true]
 rfl

theorem prefix_total (b : Slice U8) (e : Usize) (bound : e.val ≤ b.val.length) :
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
  b {«end»:=e} = ok (window b 0 e.val) := by
 simp only [core.slice.index.Slice.index,
  core.slice.index.SliceIndexRangeToUsizeSlice.index, bound, if_true]
 rfl

theorem drop_total (b : Slice U8) (s : Usize) (bound : s.val ≤ b.val.length) :
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
  b {start:=s} = ok (Slice.drop b s) := by
 simp only [core.slice.index.Slice.index,
  core.slice.index.SliceIndexRangeFromUsizeSlice.index, bound, if_true]

theorem image (b : Slice U8) (s n : Nat) :
 (window b s n).val.map byte = RSL.slice (b.val.map byte) s (s+n) := by
 rw [NMX_R3_ByteCarrier.window, show s+n-s=n by omega]
 rfl

theorem array_val {n : Usize} (a : Array U8 n) : (Array.to_slice a).val = a.val := rfl
#print axioms length
#print axioms range_total
#print axioms prefix_total
#print axioms drop_total
#print axioms image
#print axioms array_val
end NMX_R3_Slices
