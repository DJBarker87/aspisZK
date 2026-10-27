import RPu_FJh_InternalShiftsExact
import ExtractedMaskReducer
import AspisV8R15.ExactTowerBase

/-! Checked scalar fragments of the actual internal-linear callbacks.
The shift operation wraps in general; its absence of wrap is derived from
canonical source words and the proved shift bound, not assumed. -/
set_option autoImplicit false
namespace AspisR1.FJh_InternalWordOps
open Aeneas Aeneas.Std Result WP
open FIq_Native
open AspisR1.ExtractedMaskReducerOps AspisV8R17.RawReducer
abbrev M := AspisV8R15.ExactTowerBase.M31Exact
abbrev wide (x : U32) : U64 := core.convert.num.FromU64U32.from x

theorem wide_value (x : U32) : (wide x).val = x.val :=
  AspisR1.ExtractedMaskReducer.cast_widen_value x

theorem shifted_word_success (x : U32) (s : U8) (hx : x.val < P) (hs : s.val ≤ 16) :
    ∃ out : U64, (wide x <<< s : Result U64) = .ok out ∧
      out.val = x.val * 2 ^ s.val ∧ out.val < 2^47 := by
  have hpow : 2 ^ s.val ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) hs
  have hx31 : x.val < 2^31 := by norm_num [P] at hx ⊢; omega
  have hproduct : x.val * 2 ^ s.val < 2^47 := by
    calc
      x.val * 2 ^ s.val ≤ x.val * 2^16 := Nat.mul_le_mul_left _ hpow
      _ < (2^31)*2^16 := Nat.mul_lt_mul_of_pos_right hx31 (by decide)
      _ = 2^47 := by norm_num
  have hs64 : s.val < 64 := by omega
  obtain ⟨out,hrun,hvalue,_⟩ := WP.spec_imp_exists (U64.ShiftLeft_spec (wide x) s hs64)
  rw [Nat.shiftLeft_eq,U64.size,U64.numBits] at hvalue
  change out.val = ((wide x).val * 2^s.val) % 2^64 at hvalue
  have hproduct64 : x.val * 2^s.val < 2^64 := by omega
  rw [wide_value,Nat.mod_eq_of_lt hproduct64] at hvalue
  exact ⟨out,hrun,hvalue,by rw [hvalue]; exact hproduct⟩

def shiftedAdd (full : U64) (x : U32) (s : U8) : Result U64 := do
  let shifted ← wide x <<< s
  UScalar.add full shifted

theorem shiftedAdd_success (full : U64) (x : U32) (s : U8)
    (hfull : full.val < 16*P) (hx : x.val < P) (hs : s.val ≤ 16) :
    ∃ out : U64, shiftedAdd full x s = .ok out ∧
      out.val = full.val + x.val * 2^s.val ∧ out.val < 2^48 := by
  obtain ⟨shifted,hshift,hvalue,hbound⟩ := shifted_word_success x s hx hs
  have hsmall : 16*P + 2^47 < 2^48 := by norm_num [P]
  have hb : full.val + shifted.val < 2^48 := by omega
  obtain ⟨out,hrun,hout⟩ := add_success full shifted (by omega)
  refine ⟨out,?_,?_,by rw [hout]; exact hb⟩
  · simp only [shiftedAdd,hshift,bind_tc_ok,hrun]
  · rw [hout,hvalue]

def zeroSubtract (part : U64) (old : U32) : Result U64 := do
  let withP ← UScalar.add part (wide field.P)
  UScalar.sub withP (wide old)

theorem sourceP_value : (wide field.P).val = P := by
  rw [wide_value,field.P]
  rfl

theorem zeroSubtract_success (part : U64) (old : U32)
    (hpart : part.val < 16*P) (hold : old.val < P) :
    ∃ out : U64, zeroSubtract part old = .ok out ∧
      out.val = part.val + P - old.val ∧ out.val < 17*P := by
  have hsum : part.val + (wide field.P).val < 2^64 := by
    rw [sourceP_value]
    norm_num [P] at hpart ⊢
    omega
  obtain ⟨withP,hadd,hwithP⟩ := add_success part (wide field.P) hsum
  rw [sourceP_value] at hwithP
  have hsub : (wide old).val ≤ withP.val := by rw [wide_value,hwithP]; omega
  obtain ⟨out,hsubRun,hvalue⟩ := sub_success withP (wide old) hsub
  rw [hwithP,wide_value] at hvalue
  refine ⟨out,?_,hvalue,by rw [hvalue]; omega⟩
  simp only [zeroSubtract,hadd,bind_tc_ok,hsubRun]

theorem zeroSubtract_model (part : U64) (old : U32) (out : U64)
    (hold : old.val < P) (hvalue : out.val = part.val + P - old.val) :
    (out.val : M) = (part.val : M) - (old.val : M) := by
  rw [hvalue,Nat.cast_sub (by omega),Nat.cast_add]
  simp only [ZMod.natCast_self,add_zero]

#print axioms wide_value
#print axioms shifted_word_success
#print axioms shiftedAdd_success
#print axioms sourceP_value
#print axioms zeroSubtract_success
#print axioms zeroSubtract_model
end AspisR1.FJh_InternalWordOps
