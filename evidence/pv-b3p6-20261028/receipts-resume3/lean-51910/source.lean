import PV_B3P_MaskLoopBounds132
namespace PV_B3P_MaskPrefix132
open Aeneas Aeneas.Std PV_B3P_132
set_option autoImplicit false

def decode (x : reference132.Cell) : Nat × Nat := (x.row.val,x.column.val)
def prefix (out : Array reference132.Cell 3803#usize) (n : Nat) : List (Nat × Nat) :=
  (out.val.take n).map decode

theorem write_prefix (out : Array reference132.Cell 3803#usize)
    (count row column : Usize) (hn : count.val < 3803)
    (hr : row.val < 1024) (hc : column.val < 16) :
    prefix (out.set count ⟨UScalar.cast .U16 row,UScalar.cast .U8 column⟩) (count.val+1) =
      prefix out count.val ++ [(row.val,column.val)] := by
  have hi : count.val < out.val.length := by rw [out.property]; simpa using hn
  unfold prefix
  rw [Array.set_val_eq, List.take_succ_eq_append_getElem (by simpa using hi)]
  rw [List.take_set_of_le (by omega),List.getElem_set_self]
  simp only [List.map_append,List.map_cons,List.map_nil,decode]
  rw [PV_B3P_MaskCasts132.row row hr,PV_B3P_MaskCasts132.column column hc]

#print axioms write_prefix
#check Aeneas.Std.loop.eq_1
#check Aeneas.Std.loop.eq_def
end PV_B3P_MaskPrefix132
