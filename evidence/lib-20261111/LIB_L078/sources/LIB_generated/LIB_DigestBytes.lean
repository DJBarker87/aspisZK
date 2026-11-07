import LIB_DigestWord
import NND_ScalarLaws
set_option autoImplicit false
namespace LIB_DigestBytes
open Aeneas Aeneas.Std
/-- Symbolic list transport, valid at every offset and defaulting identically. -/
theorem getD (xs : List U8) (i : Nat) :
 (xs.map NND_Carrier.byte).getD i 0 = NND_Carrier.byte (xs.getD i 0#u8) := by
 induction xs generalizing i with
 | nil => cases i <;> rfl
 | cons x xs ih => cases i with
   | zero => rfl
   | succ i => exact ih i
/-- The source helper only enters these eight word positions. Out-of-range
`getElem!` is not identified with a zero-defaulting host read. -/
theorem index (xs : List U8) (i : Nat) (h : i < xs.length) :
 xs[i]! = xs.getD i 0#u8 := by
 induction xs generalizing i with
 | nil => simp at h
 | cons x xs ih => cases i with
   | zero => rfl
   | succ i => simpa using ih i (by simpa using h)
/-- SAME four bytes at every actual source word offset. -/
theorem word (b : Array U8 32#usize) (i : Nat) (bound : i < 8) :
 NND_Carrier.word (NFY_NBG_WideBytes.word b i) =
 RSL.le32 ((b.val.map NND_Carrier.byte).getD (4*i) 0)
   ((b.val.map NND_Carrier.byte).getD (4*i+1) 0)
   ((b.val.map NND_Carrier.byte).getD (4*i+2) 0)
   ((b.val.map NND_Carrier.byte).getD (4*i+3) 0) := by
 have len : b.val.length = 32 := b.property
 unfold NFY_NBG_WideBytes.word
 rw [LIB_DigestWord.four,getD,getD,getD,getD]
 simp (disch := omega) only [index]
#print axioms getD
#print axioms index
#print axioms word
end LIB_DigestBytes
