import Port4B_NativeLeaf

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_KeyDecode
open Aeneas Aeneas.Std Result
open Port4B_NativeLeaf

theorem high (key : U64) : (decodedIndex key).val=(key.val/256)%4294967296 := by
  unfold decodedIndex
  rw [UScalar.cast_val_eq]
  change (key.bv.ushiftRight 8).toNat % 4294967296 = _
  change (key.val >>> 8) % 4294967296 = _
  rw [Nat.shiftRight_eq_div_pow]

theorem low (key : U64) : (UScalar.cast .Usize (key &&& 255#u64)).val=key.val%256 := by
  rw [UScalar.cast_val_eq,UScalar.val_and]
  have mask : key.val &&& (255#u64).val=key.val%256 := by
    exact Nat.and_two_pow_sub_one_eq_mod key.val 8
  rw [mask]
  apply Nat.mod_eq_of_lt
  have cap : 256<2^UScalarTy.Usize.numBits := by scalar_tac
  omega

theorem packed (q : Fin 22 → Fin 262144) (batch kind pos : Nat)
    (mem : pos∈OraclePortSelectedDraft.batchPositions batch) (lo : Usize)
    (base : lo.val=(if batch=0 then 0 else 10)) :
    (decodedIndex (MultiproofConeSortOrder.packed q batch kind pos)).val=
      OraclePortSelectedDraft.index q kind pos ∧
    (openingIndex lo (MultiproofConeSortOrder.packed q batch kind pos)).val=pos := by
  have ib : OraclePortSelectedDraft.index q kind pos<262144 := by
    simp only [OraclePortSelectedDraft.index]
    have h := (q ⟨pos%22,Nat.mod_lt _ (by decide)⟩).isLt
    split <;> omega
  constructor
  · rw [high,MultiproofConeKeyAdapters.packed_index q batch kind pos mem,
      Nat.mod_eq_of_lt (by omega)]
  · unfold openingIndex
    rw [Usize.wrapping_add_val_eq,low,base]
    rw [MultiproofConeKeyAdapters.packed_opening q batch kind pos mem]
    apply Nat.mod_eq_of_lt
    have bounds := MultiproofConeKeyAdapters.position_bounds batch pos mem
    have cap : 22<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
    omega

#print axioms high
#print axioms low
#print axioms packed
end AspisR1.Port4B_KeyDecode
end
