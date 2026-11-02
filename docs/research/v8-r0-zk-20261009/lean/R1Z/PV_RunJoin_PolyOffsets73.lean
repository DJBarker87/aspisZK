import R1Z.PV_RunJoin_ByteSlice40
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PolyOffsets73
open Aeneas Aeneas.Std Result

theorem offsets (i : Usize) (hi : i.val<28) :
    (Usize.wrapping_mul 32#usize i).val=32*i.val ∧
    (Usize.wrapping_add (Usize.wrapping_mul 32#usize i) 32#usize).val=32*i.val+32 := by
  have size : 1024<UScalar.size .Usize := by
    have lower : 2^32≤UScalar.size .Usize := by
      rw [UScalar.size_def]
      exact Nat.pow_le_pow_right (by decide) System.Platform.le_numBits
    omega
  have hm : (Usize.wrapping_mul 32#usize i).val=32*i.val := by
    rw [Usize.wrapping_mul_val_eq]
    change (32*i.val)%UScalar.size .Usize=32*i.val
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨hm,?_⟩
  rw [Usize.wrapping_add_val_eq,hm]
  change (32*i.val+32)%UScalar.size .Usize=32*i.val+32
  exact Nat.mod_eq_of_lt (by omega)

theorem divide (s : Slice U8) (hlen : s.length=896) :
    Slice.len s / 32#usize=ok 28#usize := by
  have len : Slice.len s=896#usize := UScalar.eq_of_val_eq hlen
  rw [len]
  obtain ⟨d,hd,hv⟩ := UScalar.div_spec 896#usize (y:=32#usize) (by decide)
  have eq : d=28#usize := UScalar.eq_of_val_eq hv
  exact hd.trans (congrArg Result.ok eq)

#print axioms offsets
#print axioms divide
end R1Z.PV_RunJoin_PolyOffsets73
