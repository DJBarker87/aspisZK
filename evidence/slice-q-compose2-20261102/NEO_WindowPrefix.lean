import NEO_ComplexReference
set_option autoImplicit false
namespace NEO_WindowPrefix
open Aeneas Aeneas.Std Result

theorem index (bytes : Slice U8) (n k : Usize) (bound : n.val ≤ bytes.val.length)
 (inside : k.val<n.val) :
 Slice.index_usize bytes k =
 Slice.index_usize (NEO_PrefixSlices.headArray bytes n bound).to_slice k := by
 have total : k.val<bytes.val.length := by omega
 simp [Slice.index_usize,NEO_PrefixSlices.headArray,Array.to_slice,total,inside,
  List.length_take,Nat.min_eq_left bound]

theorem word (bytes : Slice U8) (n i : Usize) (bound : n.val ≤ bytes.val.length)
 (h0 : i.val<n.val)
 (h1 : (Usize.wrapping_add i 1#usize).val<n.val)
 (h2 : (Usize.wrapping_add i 2#usize).val<n.val)
 (h3 : (Usize.wrapping_add i 3#usize).val<n.val) :
 NEO_WindowV2.word bytes i =
 NEO_WindowV2.word (NEO_PrefixSlices.headArray bytes n bound).to_slice i := by
 simp only [NEO_WindowV2.word,lift,bind_tc_ok,index bytes n i bound h0,
  index bytes n (Usize.wrapping_add i 1#usize) bound h1,
  index bytes n (Usize.wrapping_add i 2#usize) bound h2,
  index bytes n (Usize.wrapping_add i 3#usize) bound h3]

theorem wrap_small (i j : Usize) (h : i.val+j.val<8) :
 (Usize.wrapping_add i j).val<8 := by
 rw [Usize.wrapping_add_val_eq]
 change (i.val+j.val)%UScalar.size .Usize<8
 have cap : 8<UScalar.size .Usize := by rw [UScalar.size_def]; scalar_tac
 rw [Nat.mod_eq_of_lt (by omega)]
 exact h

theorem complex (bytes : Slice U8) (bound : 8≤bytes.val.length) :
 NEO_WindowV2.complex bytes =
 NEO_WindowV2.complex (NEO_PrefixSlices.headArray bytes 8#usize bound).to_slice := by
 have a := word bytes 8#usize 0#usize bound (by decide) (wrap_small _ _ (by decide)) (wrap_small _ _ (by decide)) (wrap_small _ _ (by decide))
 have b := word bytes 8#usize 4#usize bound (by decide) (wrap_small _ _ (by decide)) (wrap_small _ _ (by decide)) (wrap_small _ _ (by decide))
 simp only [NEO_WindowV2.complex,a,b]

#print axioms index
#print axioms word
#print axioms wrap_small
#print axioms complex
end NEO_WindowPrefix
