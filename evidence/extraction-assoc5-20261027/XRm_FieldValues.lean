import XRm_Reduce
import XRm_M31Canonical
import XRk_ResultTools
import Mathlib.Data.ZMod.Basic
open Aeneas Aeneas.Std Result
open XRk_ResultTools XRm_Reduce
namespace XRm_FieldValues
abbrev M31Exact := ZMod m31Modulus
theorem cast_two31_eq_one :
    ((2 ^ 31 : Nat) : M31Exact) = 1 := by
  have h : 2 ^ 31 = m31Modulus + 1 := by
    norm_num [m31Modulus]
  rw [h, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]

theorem residue_mersenneFold31 (x : Nat) :
    ((mersenneFold31 x : Nat) : M31Exact) = (x : M31Exact) := by
  rw [mersenneFold31, Nat.cast_add]
  calc
    ((x % 2 ^ 31 : Nat) : M31Exact) +
          ((x / 2 ^ 31 : Nat) : M31Exact) =
        ((x % 2 ^ 31 : Nat) : M31Exact) +
          ((x / 2 ^ 31 : Nat) : M31Exact) *
            ((2 ^ 31 : Nat) : M31Exact) := by
              rw [cast_two31_eq_one, mul_one]
    _ = ((x % 2 ^ 31 + (x / 2 ^ 31) * 2 ^ 31 : Nat) : M31Exact) := by
          rw [Nat.cast_add, Nat.cast_mul]
    _ = (x : M31Exact) := by rw [Nat.mod_add_div']

theorem residue_rawM31ReduceU64 (x : Nat) :
    ((rawM31ReduceU64 x : Nat) : M31Exact) = (x : M31Exact) := by
  by_cases hhigh :
      m31Modulus ≤ mersenneFold31 (mersenneFold31 x)
  · rw [rawM31ReduceU64, if_pos hhigh, Nat.cast_sub hhigh,
      ZMod.natCast_self, sub_zero, residue_mersenneFold31,
      residue_mersenneFold31]
  · rw [rawM31ReduceU64, if_neg hhigh, residue_mersenneFold31,
      residue_mersenneFold31]


theorem reduce_value (x : U64) (out : U32)
    (run : XRk_Field.field.reduce_u64 x=ok out) :
    (out.val : M31Exact)=(x.val : M31Exact) := by
  have same := Result.ok.inj ((extracted_reduce_u64_eq_out x).symm.trans run)
  rw [←same,extractedReduceOut_val,residue_rawM31ReduceU64]

theorem sub_val (a b : U32) (h : b.val≤a.val) :
    (a.wrapping_sub b).val=a.val-b.val := by
  change (UScalar.overflowing_sub a b).fst.val = _
  have hn : ¬a.val<b.val := by omega
  have hs := UScalar.overflowing_sub_eq a b
  simp only [hn,↓reduceIte] at hs
  exact hs.1

theorem add_val (a b : U32) (h : a.val+b.val<4294967296) :
    (a.wrapping_add b).val=a.val+b.val := by
  rw [U32.wrapping_add_val_eq,u32_size_eq,show u32Cardinality=4294967296 by norm_num [u32Cardinality],Nat.mod_eq_of_lt h]

theorem add (a b out : U32) (ha : a<2147483647#u32) (hb : b<2147483647#u32)
    (run : XRk_Field.field.M31.add a b=ok out) :
    (out.val : M31Exact)=(a.val : M31Exact)+(b.val : M31Exact) := by
  have hs := add_val a b (by scalar_tac)
  have hp : ((2147483647#u32).val : M31Exact)=0 := ZMod.natCast_self _
  unfold XRk_Field.field.M31.add XRk_Field.field.P at run
  simp only [lift,bind_tc_ok] at run
  split at run
  · rename_i high
    cases Result.ok.inj run
    have hd := sub_val (a.wrapping_add b) 2147483647#u32 high
    change ((_ : Nat) : M31Exact)=_
    rw [hd,Nat.cast_sub high,hs,Nat.cast_add,hp,sub_zero]
  · cases Result.ok.inj run
    change ((_ : Nat) : M31Exact)=_
    rw [hs,Nat.cast_add]

theorem sub (a b out : U32) (ha : a<2147483647#u32) (hb : b<2147483647#u32)
    (run : XRk_Field.field.M31.sub a b=ok out) :
    (out.val : M31Exact)=(a.val : M31Exact)-(b.val : M31Exact) := by
  have hpv : (2147483647#u32).val=2147483647 := rfl
  have hp : ((2147483647#u32).val : M31Exact)=0 := ZMod.natCast_self _
  have hs := add_val a 2147483647#u32 (by scalar_tac)
  have hnb : b.val≤(a.wrapping_add 2147483647#u32).val := by rw [hs]; scalar_tac
  have hd := sub_val (a.wrapping_add 2147483647#u32) b hnb
  unfold XRk_Field.field.M31.sub XRk_Field.field.P at run
  simp only [lift,bind_tc_ok] at run
  split at run
  · rename_i high
    cases Result.ok.inj run
    have he := sub_val ((a.wrapping_add 2147483647#u32).wrapping_sub b) 2147483647#u32 high
    change ((_ : Nat) : M31Exact)=_
    rw [he,Nat.cast_sub high,hd,Nat.cast_sub hnb,hs,Nat.cast_add,hp,add_zero,sub_zero]
  · cases Result.ok.inj run
    change ((_ : Nat) : M31Exact)=_
    rw [hd,Nat.cast_sub hnb,hs,Nat.cast_add,hp,add_zero]

theorem mul (a b out : U32)
    (run : XRk_Field.field.M31.mul a b=ok out) :
    (out.val : M31Exact)=(a.val : M31Exact)*(b.val : M31Exact) := by
  unfold XRk_Field.field.M31.mul at run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨r,hr,run⟩ := bind_success _ _ _ run
  cases Result.ok.inj run
  have bound : a.val*b.val<18446744073709551616 := by
    have ha : a.val<4294967296 := by scalar_tac
    have hb : b.val<4294967296 := by scalar_tac
    have h := Nat.mul_lt_mul_of_lt_of_lt ha hb
    exact h
  have hv : (U64.wrapping_mul (UScalar.cast .U64 a) (UScalar.cast .U64 b)).val=a.val*b.val := by
    rw [U64.wrapping_mul_val_eq,U32.cast_U64_val_eq,U32.cast_U64_val_eq,
      u64_size_eq,show u64Cardinality=18446744073709551616 by norm_num [u64Cardinality],Nat.mod_eq_of_lt bound]
  rw [reduce_value _ _ hr,hv,Nat.cast_mul]

#print axioms cast_two31_eq_one
#print axioms residue_mersenneFold31
#print axioms residue_rawM31ReduceU64
#print axioms reduce_value
#print axioms sub_val
#print axioms add_val
#print axioms add
#print axioms sub
#print axioms mul
end XRm_FieldValues
