import Port4B_AnyFalse

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_ByteWord
open Aeneas Aeneas.Std Result

/-- Symbolic little-endian zero decoding, for arbitrary word widths.
This reasons about one requested bit rather than evaluating a concrete word. -/
theorem fromLE_zero (bs : List (BitVec 8)) (zero : BitVec.fromLEBytes bs=0) :
    ∀ b∈bs, b=0 := by
  intro b mem
  obtain ⟨j,hj,same⟩ := List.mem_iff_getElem.mp mem
  apply (Byte.eq_iff b 0).mpr
  intro k hk
  have read := congrArg (fun word : BitVec (8*bs.length) => word[8*j+k]!) zero
  rw [BitVec.fromLEBytes_getElem!] at read
  have div : (8*j+k)/8=j := by omega
  have mod : (8*j+k)%8=k := by omega
  have element : bs[j]! = b := (getElem!_pos bs j hj).trans same
  rw [div,mod,element] at read
  have zeroNat (w : Nat) : (0 : BitVec w).toNat=0 := rfl
  simp only [BitVec.getElem!_eq_testBit_toNat,Byte.testBit,zeroNat,
    Nat.zero_testBit] at read ⊢
  exact read

/-- A zero native u64 word forces all eight original bytes to be zero. -/
theorem u64_zero (word : Array U8 8#usize)
    (zero : core.num.U64.from_le_bytes word=0#u64) : ∀ b∈word.val, b=0#u8 := by
  have bits := congrArg UScalar.bv zero
  have width : 8*(word.val.map U8.bv).length=64 := by simp only [List.length_map,word.property];rfl
  change (BitVec.fromLEBytes (word.val.map U8.bv)).cast width = 0 at bits
  have raw : BitVec.fromLEBytes (word.val.map U8.bv)=0 := by
    have eq := congrArg BitVec.toNat bits
    rw [BitVec.toNat_cast] at eq
    apply BitVec.eq_of_toNat_eq
    simpa using eq

  intro b mem
  have zeroByte := fromLE_zero (word.val.map U8.bv) raw b.bv (List.mem_map.mpr ⟨b,mem,rfl⟩)
  apply UScalar.eq_of_val_eq
  exact congrArg BitVec.toNat zeroByte

#print axioms fromLE_zero
#print axioms u64_zero
end AspisR1.Port4B_ByteWord
end
