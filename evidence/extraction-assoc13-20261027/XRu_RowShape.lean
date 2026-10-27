import XRn_Join_Funs
import S7Kani2OwnedRow
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRu_RowShape
abbrev Row := Array U64 4#usize
abbrev Limbs := Array U32 4#usize
/-- A four-cell array has exactly four values; no numeral recurrence reduces. -/
theorem cells (row : Row) : ∃ a b c d : U64, row=Array.make 4#usize [a,b,c,d] := by
 have len : row.val.length=4 := row.property
 have shape : ∃ a b c d : U64, row.val=[a,b,c,d] := by
  generalize hx : row.val=xs at len ⊢
  cases xs with
  | nil => simp_all
  | cons a xs =>
   cases xs with
   | nil => simp_all
   | cons b xs =>
    cases xs with
    | nil => simp_all
    | cons c xs =>
     cases xs with
     | nil => simp_all
     | cons d xs =>
      cases xs with
      | nil => exact ⟨a,b,c,d,rfl⟩
      | cons e xs => simp only [List.length_cons] at len; omega
 obtain ⟨a,b,c,d,h⟩ := shape
 exact ⟨a,b,c,d,Subtype.ext h⟩
/-- Actual range-next at one of the four cells, with its checked increment. -/
theorem range (i j : Usize) (lt : i.val<4) (inc : j.val=i.val+1) :
 core.iter.range.IteratorRange.next core.iter.range.StepUsize {start:=i,«end»:=4#usize} =
 ok (some i,{start:=j,«end»:=4#usize}) := by
 obtain ⟨v,hv,he⟩ := WP.spec_imp_exists
  (core.iter.range.IteratorRange.next_Usize_some_spec {start:=i,«end»:=4#usize} lt)
 rcases v with ⟨o,r⟩
 rcases he with ⟨ho,hr,hend⟩
 have hs : r.start=j := UScalar.eq_imp r.start j (by change r.start.val=i.val+1 at hr; omega)
 have rr : r={start:=j,«end»:=4#usize} := by cases r; simp_all
 simpa only [ho,rr] using hv
#print axioms cells
#print axioms range
end XRu_RowShape
