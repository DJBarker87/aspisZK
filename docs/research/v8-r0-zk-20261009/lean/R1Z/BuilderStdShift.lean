import R1Z.BuilderStdModels

set_option autoImplicit false
namespace R1Z.BuilderStdModels
open Aeneas Aeneas.Std Result

/-- The pinned backend takes a U32 shift count; Rust's usize count has
identical low six bits after this cast, even outside the admitted range. -/
def shift64 (x : Std.U64) (n : Std.Usize) : Std.U64 :=
  Std.U64.wrapping_shr x (UScalar.cast .U32 n)

theorem shift_count_mod64 (n : Std.Usize) :
    (UScalar.cast .U32 n).val % 64 = n.val % 64 := by
  rw [UScalar.cast_val_eq]
  change n.val % (2^32) % 64 = n.val % 64
  exact Nat.mod_mod_of_dvd n.val (by norm_num : 64 ∣ 2^32)

theorem shift64_spec (x : Std.U64) (n : Std.Usize) :
    shift64 x n = ⟨x.bv.ushiftRight (n.val % 64)⟩ := by
  unfold shift64 Std.U64.wrapping_shr UScalar.wrapping_shr
  change (⟨x.bv.ushiftRight ((UScalar.cast .U32 n).val % 64)⟩ : Std.U64) = _
  rw [shift_count_mod64]

theorem shift64_one_spec (x : Std.U64) :
    Std.U64.wrapping_shr x 1#u32 = ⟨x.bv.ushiftRight 1⟩ := rfl

#print axioms shift_count_mod64
#print axioms shift64_spec
#print axioms shift64_one_spec
end R1Z.BuilderStdModels
