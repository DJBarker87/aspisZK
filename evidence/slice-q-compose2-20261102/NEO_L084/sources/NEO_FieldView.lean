import NEO_WideTotal
set_option autoImplicit false
namespace NEO_FieldView
open Aeneas Aeneas.Std Result AspisR1

def start (i : Usize) := Usize.wrapping_mul i 32#usize
def finish (i : Usize) := Usize.wrapping_mul (Usize.wrapping_add i 1#usize) 32#usize

theorem addresses (i : Usize) (small : i.val<262144) :
 (start i).val=32*i.val ∧ (finish i).val=32*i.val+32 := by
 have cap : 8388609<UScalar.size .Usize := by rw [UScalar.size_def]; scalar_tac
 have add : (Usize.wrapping_add i 1#usize).val=i.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  change (i.val+1)%UScalar.size .Usize=i.val+1
  exact Nat.mod_eq_of_lt (by omega)
 constructor
 · unfold start
   rw [Usize.wrapping_mul_val_eq]
   change (i.val*32)%UScalar.size .Usize=32*i.val
   rw [Nat.mod_eq_of_lt (by omega)]
   omega
 · unfold finish
   rw [Usize.wrapping_mul_val_eq]
   change ((Usize.wrapping_add i 1#usize).val*32)%UScalar.size .Usize=32*i.val+32
   rw [add,Nat.mod_eq_of_lt (by omega)]
   omega

theorem result (bytes : Slice U8) (i : Usize) (small : i.val<262144)
 (fit : 32*i.val+32≤bytes.val.length) :
 FIo_Native.weights.field bytes i =
 (do let parsed ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
       (NEO_FixedWindow.window bytes (start i).val 32#usize (by have h:=addresses i small; omega)).to_slice
     core.option.Option.unwrap parsed) := by
 have h:=addresses i small
 have slice:=NEO_FixedWindow.range bytes (start i) (finish i) 32#usize
  (by omega) (by omega) (by change (finish i).val-(start i).val=32; omega)
 simp only [FIo_Native.weights.field,lift,bind_tc_ok]
 change (do let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes {start:=start i,«end»:=finish i}
            let o ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes s
            core.option.Option.unwrap o)=_
 rw [slice,bind_tc_ok]

#print axioms addresses
#print axioms result
end NEO_FieldView
