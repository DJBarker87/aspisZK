import LPn_DecodeResult
open Aeneas Aeneas.Std Result LPl_Kit_Release LPl_Kit_FieldExternal
set_option autoImplicit false
namespace LPn.Decode

theorem error_bound (N : Usize) (r : r1_wire.ValidatedRecord) (off : Usize)
    (ready : Ready N r off) (size : r.framed.val.length≤3717) (i : Nat)
    (scan : LPl.Scan.Trace (predicate (r.framed.val.drop 5) (off.val*32) N.val) N.val 0 (some i)) :
    off.val+i<116 ∧ off.val+i≤UScalar.cMax .Usize := by
  have hit := (LPl.Scan.first_error _ _ _ scan).symm
  simp only [predicate] at hit
  have live := LPn.DecodeModel.first_error_bound (r.framed.val.drop 5) (off.val*32) N.val i hit
  have fits := ready.range
  simp only [List.length_drop] at fits
  have small : off.val+i<116 := by omega
  exact ⟨small,by scalar_tac⟩

/-- Exact provenance observation at the token constructor. This is local
    getter identity, not another proof of Prefix::parse. -/
structure Token (p : r1_wire.Prefix) (row : U8) (r : r1_wire.ValidatedRecord) : Prop where
  row_eq : r.row=row
  framed_eq : r.framed=p.records.val[row.val]?.getD ⟨[],by simp⟩

theorem token_unique (p : r1_wire.Prefix) (row : U8) (r s : r1_wire.ValidatedRecord)
    (hr : Token p row r) (hs : Token p row s) : r=s := by
  have rows := hr.row_eq.trans hs.row_eq.symm
  have frames := hr.framed_eq.trans hs.framed_eq.symm
  cases r;cases s
  cases rows;cases frames;rfl

#print axioms error_bound
#print axioms token_unique
end LPn.Decode
