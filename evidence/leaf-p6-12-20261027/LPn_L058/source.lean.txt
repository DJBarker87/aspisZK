import LPn_DecodeOutput
open Aeneas Aeneas.Std Result LPl_Kit_Release LPl_Kit_FieldExternal
set_option autoImplicit false
namespace LPn.Decode

/-- Exact scalar native guard success conditions, separated from local decode
    observations. They are tested by K005, not a canonicality antecedent. -/
structure Ready (N : Usize) (r : r1_wire.ValidatedRecord) (off : Usize) : Prop where
  row : ¬ r.row < 14#u8
  arithmetic : ¬ (off.val*32>Usize.max ∨ N.val*32>Usize.max ∨ off.val*32+N.val*32>Usize.max)
  framed : ¬ r.framed.val.length<5
  range : ¬ off.val*32+N.val*32>(r.framed.val.drop 5).length

theorem native_success (N : Usize) (r : r1_wire.ValidatedRecord) (off : Usize)
    (initial : List Q) (a : Array Q N) (ready : Ready N r off)
    (size : initial.length=N.val)
    (scan : LPl.Scan.Trace (predicate (r.framed.val.drop 5) (off.val*32) N.val) N.val 0 none)
    (writes : Trace (r.framed.val.drop 5) (off.val*32) initial N.val a.val) :
    r1_wire.ValidatedRecord.decode_k N r off = ok (.Ok a) := by
  have noerr := (LPl.Scan.first_error _ _ _ scan).symm
  have values := (output _ _ initial a.val N.val writes size).symm
  rw [LPn.DecodeModel.shipped_leaf_model]
  simp only [if_neg ready.row,if_neg ready.arithmetic,if_neg ready.framed,if_neg ready.range]
  change LPl_A.firstBad (fun i => !predicate (r.framed.val.drop 5) (off.val*32) N.val i) N.val = none at noerr
  rw [noerr,values]
  simp [a.property]

theorem native_error (N : Usize) (r : r1_wire.ValidatedRecord) (off : Usize)
    (ready : Ready N r off) (i : Nat)
    (scan : LPl.Scan.Trace (predicate (r.framed.val.drop 5) (off.val*32) N.val) N.val 0 (some i))
    (bound : off.val+i ≤ UScalar.cMax .Usize) :
    r1_wire.ValidatedRecord.decode_k N r off =
      ok (.Err (.NonCanonical r.row (UScalar.ofNat (off.val+i) bound))) := by
  have hit := (LPl.Scan.first_error _ _ _ scan).symm
  rw [LPn.DecodeModel.shipped_leaf_model]
  simp only [if_neg ready.row,if_neg ready.arithmetic,if_neg ready.framed,if_neg ready.range]
  change LPl_A.firstBad (fun j => !predicate (r.framed.val.drop 5) (off.val*32) N.val j) N.val = some i at hit
  rw [hit]
  simp [bound]

theorem row_error (N : Usize) (r : r1_wire.ValidatedRecord) (off : Usize)
    (bad : r.row<14#u8) :
    r1_wire.ValidatedRecord.decode_k N r off = ok (.Err .InvalidRow) := by
  rw [LPn.DecodeModel.shipped_leaf_model];simp [bad]

theorem arithmetic_error (N : Usize) (r : r1_wire.ValidatedRecord) (off : Usize)
    (row : ¬ r.row<14#u8)
    (bad : off.val*32>Usize.max ∨ N.val*32>Usize.max ∨ off.val*32+N.val*32>Usize.max) :
    r1_wire.ValidatedRecord.decode_k N r off = ok (.Err (.Length r.row)) := by
  rw [LPn.DecodeModel.shipped_leaf_model];simp [row,bad]

theorem range_error (N : Usize) (r : r1_wire.ValidatedRecord) (off : Usize)
    (row : ¬ r.row<14#u8)
    (arithmetic : ¬ (off.val*32>Usize.max ∨ N.val*32>Usize.max ∨ off.val*32+N.val*32>Usize.max))
    (framed : ¬ r.framed.val.length<5)
    (bad : off.val*32+N.val*32>(r.framed.val.drop 5).length) :
    r1_wire.ValidatedRecord.decode_k N r off = ok (.Err (.Length r.row)) := by
  rw [LPn.DecodeModel.shipped_leaf_model];simp [row,arithmetic,framed,bad]

#print axioms native_success
#print axioms native_error
#print axioms row_error
#print axioms arithmetic_error
#print axioms range_error
end LPn.Decode
