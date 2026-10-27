import R1Z.PV_CB3_StagedTotal
set_option autoImplicit false
namespace R1Z.PV_CB3_StagedPacking
open Aeneas Aeneas.Std

def bits {n : Usize} (a : Array U32 n) : List (BitVec 32) := a.val.map UScalar.bv

theorem bits_length {n : Usize} (a : Array U32 n) : (bits a).length = n.val := by
  simp only [bits,List.length_map,a.property]

def pack {n : Usize} (xs : List (BitVec 32)) (h : xs.length = n.val) : Array U32 n :=
  ⟨xs.map (fun x => (⟨x⟩ : U32)),by simpa only [List.length_map] using h⟩

theorem bits_pack {n : Usize} (xs : List (BitVec 32)) (h : xs.length = n.val) :
    bits (pack xs h) = xs := by
  simp [bits,pack,List.map_map]

theorem word_eta (x : U32) : (⟨x.bv⟩ : U32) = x := by
  apply UScalar.eq_of_val_eq
  exact UScalar.bv_toNat x

theorem pack_bits {n : Usize} (a : Array U32 n) : pack (bits a) (bits_length a) = a := by
  apply Subtype.ext
  simp [pack,bits,List.map_map,Function.comp_def,word_eta]
#print axioms word_eta
#print axioms bits_length
#print axioms bits_pack
#print axioms pack_bits
end R1Z.PV_CB3_StagedPacking
