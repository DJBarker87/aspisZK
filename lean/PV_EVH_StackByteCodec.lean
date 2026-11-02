import PV_EVH_StackEntropyFill
set_option autoImplicit false
noncomputable section
namespace PV_EVH_StackByteCodec
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_StackZero (Slot State)

/-- The physical byte encoding does not lose any of the source U8 value.
This is a symbolic bounded-scalar law, not reduction of an entropy array. -/
theorem lossless (x : U8) : (UInt8.ofNat x.val).toNat = x.val := by
  change x.val % 256 = x.val
  have hs : UScalar.size .U8 = 256 := by rw [UScalar.size_def]; rfl
  have hx := x.hSize
  rw [hs] at hx
  exact Nat.mod_eq_of_lt hx

theorem encode_read {n : Usize} (a : Array U8 n) (i : Nat) (x : U8)
    (h : a.val[i]? = some x) :
    ((PV_EVH_StackEntropyFill.encode a)[i]?.getD 0).toNat = x.val := by
  have he : (PV_EVH_StackEntropyFill.encode a)[i]? = some (UInt8.ofNat x.val) := by
    simp only [PV_EVH_StackEntropyFill.encode,List.getElem?_map,h,Option.map_some]
  rw [he]
  exact lossless x

/-- Actual post-fill physical memory and the corresponding source scalar
agree at each initialized index. The original slot address is never derived
from scalar equality; its source-frame association remains a separate P. -/
theorem post_read [ExternalTypes] (slot : Slot) (d : PV_EVH_StackEntropyFill.Delivery)
    (w : State) (i : Nat) (x : U8) (hi : i < slot.initialized)
    (hx : d.buffer.val[i]? = some x) :
    (PV_EVH_StackEntropyFill.post slot d w).memory (slot.address+i) = x.val := by
  exact (PV_EVH_StackEntropyFill.physical_buffer slot d w i hi).trans
    (encode_read d.buffer i x hx)

theorem copied_read {n : Usize} (a : Array U8 n) (w : State) (address i : Nat) (x : U8)
    (hm : w.memory (address+i) = ((PV_EVH_StackEntropyFill.encode a)[i]?.getD 0).toNat)
    (hx : a.val[i]? = some x) : w.memory (address+i) = x.val :=
  hm.trans (encode_read a i x hx)

#print axioms lossless
#print axioms encode_read
#print axioms post_read
#print axioms copied_read
end PV_EVH_StackByteCodec
