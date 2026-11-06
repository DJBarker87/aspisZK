import NKQ_ArrayWindows
set_option autoImplicit false
namespace AspisR1.NKQ_ReadTwo
open Aeneas Aeneas.Std Result NKQ_ArrayWindows

theorem readTwo {α : Type} {n m : Usize} (a : Array (Array α m) n)
 (row col : Usize) (hr : row.val<n.val) (hc : col.val<m.val) :
 (do let inner ← Array.index_usize a row
     let value ← Array.index_usize inner col
     ok (value,a)) = ok (cell (cell a row.val hr) col.val hc,a) := by
 rw [read a row hr,bind_tc_ok,read (cell a row.val hr) col hc,bind_tc_ok]

#print axioms readTwo
end AspisR1.NKQ_ReadTwo
