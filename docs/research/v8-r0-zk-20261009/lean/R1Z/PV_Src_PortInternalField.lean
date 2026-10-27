import R1Z.PV_Src_PortInternalCells
import R0Z.PoseidonInternal

/-! Field meaning of each nonzero internal-linear source lane. The actual
unreduced U64 sum is retained; only its explicit source bound is required. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortInternalField
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortInternalStep

theorem shifts_bound (j : Fin 15) :
    (poseidon2.INTERNAL_SHIFTS.val[j.val]!).val ≤ 16 := by
  fin_cases j <;> simp only [poseidon2.INTERNAL_SHIFTS] <;> decide

theorem shifts_model (j : Fin 15) :
    (poseidon2.INTERNAL_SHIFTS.val[j.val]!).val = R0P.poseidonInternalShifts j := by
  fin_cases j <;> simp only [poseidon2.INTERNAL_SHIFTS,R0P.poseidonInternalShifts] <;> rfl

theorem mixed_value (full : U64) (x sh : U32)
    (hf : full.val < 68719476736) (hs : sh.val ≤ 16) :
    (U64.wrapping_add full (U64.wrapping_shl (UScalar.cast .U64 x) sh)).val =
      full.val + x.val * 2^sh.val := by
  have hsh := shl64 (UScalar.cast .U64 x) sh (by rw [c64];exact u32lt x) hs
  rw [c64] at hsh
  have hb : x.val * 2^sh.val < 281474976710656 := by
    have h1 := Nat.mul_le_mul_left x.val (Nat.pow_le_pow_right (by decide : 1 ≤ (2:Nat)) hs)
    have h2 := Nat.mul_lt_mul_of_pos_right (u32lt x) (by decide : 0 < (2:Nat)^16)
    norm_num only [Nat.reducePow,Nat.reduceMul] at h1 h2
    omega
  exact add64v _ _ _ _ rfl hsh (by omega)

variable {K : Type} [Field K] [CharP K 2147483647]

theorem cell_lift (state : State) (full : U64) (index : Usize)
    (lo : 1 ≤ index.val) (hi : index.val < 16) (hf : full.val < 68719476736) :
    liftU (K := K) (cell state full index) =
      (full.val : K) + liftU state.val[index.val]! *
        ((2^((poseidon2.INTERNAL_SHIFTS.val[index.val-1]!).val) : Nat) : K) := by
  have hs := shifts_bound ⟨index.val-1,by omega⟩
  have cast : (UScalar.cast .U32 poseidon2.INTERNAL_SHIFTS.val[index.val-1]!).val =
      (poseidon2.INTERNAL_SHIFTS.val[index.val-1]!).val := by scalar_tac
  unfold cell liftU
  rw [PV_Src_ScalarReduce.modulo,mixed_value full _ _ hf (by rw [cast];exact hs),cast]
  rw [cast_mod,Nat.cast_add,Nat.cast_mul]

#print axioms shifts_bound
#print axioms shifts_model
#print axioms mixed_value
#print axioms cell_lift
end R1Z.PV_Src_PortInternalField
