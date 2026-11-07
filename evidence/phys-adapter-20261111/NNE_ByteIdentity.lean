import NNE_Entry
set_option autoImplicit false
namespace NNE_ByteIdentity
open Aeneas Aeneas.Std AspisR1.S2W_ReturnedCheckpoint

theorem byte (a b : U8) (h : nativeByte a = nativeByte b) : a = b := by
 have hv := congrArg UInt8.toNat h
 have hv' : a.val = b.val := by
  simpa only [nativeByte,UInt8.toNat_ofNat_of_lt' a.bv.isLt,
   UInt8.toNat_ofNat_of_lt' b.bv.isLt] using hv
 exact UScalar.eq_of_val_eq hv'

theorem list (a b : List U8) (h : a.map nativeByte = b.map nativeByte) : a = b := by
 induction a generalizing b with
 | nil => cases b <;> simp_all
 | cons a as ih =>
  cases b with
  | nil => simp at h
  | cons b bs =>
   have hs := List.cons.inj h
   rw [byte a b hs.1,ih bs hs.2]

theorem slice (a b : Slice U8) (h : nativeBytes a = nativeBytes b) : a = b := by
 have hv := list a.val b.val h
 cases a; cases b
 simp_all
#print axioms byte
#print axioms list
#print axioms slice
end NNE_ByteIdentity
