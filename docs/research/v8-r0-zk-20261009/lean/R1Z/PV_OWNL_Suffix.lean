import R1Z.PV_OWNJ_Rows
import Mathlib.Algebra.BigOperators.Field
set_option autoImplicit false
namespace R1Z.PV_OWNL_Suffix
open PV_OWNI_RawOps PV_OWNI_Scanner

theorem head_bit (x : Q) (xs : List Q) :
 (bits (x::xs)).testBit xs.length = equal x one := by
 have hb := bits_bound xs
 cases h : equal x one <;>
  simp only [bits,h,Bool.false_eq_true,if_false,if_true,Nat.zero_mul,Nat.one_mul,
   Nat.zero_add,Nat.testBit_two_pow_add_eq,Nat.testBit_lt_two_pow hb,Bool.not_false]

theorem tail_bit (x : Q) (xs : List Q) (i : Nat) (hi : i < xs.length) :
 (bits (x::xs)).testBit i = (bits xs).testBit i := by
 have hr : bits (x::xs) % 2^xs.length = bits xs := by
  exact Nat.mul_add_mod_of_lt (bits_bound xs)
 have h := congrArg (fun n : Nat => n.testBit i) hr
 simpa only [Nat.testBit_mod_two_pow,show decide (i < xs.length) = true from by simp [hi],
  Bool.true_and] using h

theorem decoded_bits {K : Type} [Zero K] [One K] (decode : Q → K)
 (hz : decode zero = 0) (ho : decode one = 1) (xs : List Q)
 (hb : ∀ x ∈ xs, boolean x = true) (i : Fin xs.length) :
 decode (xs.get i) = if (bits xs).testBit (xs.length-1-i.val) then 1 else 0 := by
 induction xs with
 | nil => exact Fin.elim0 i
 | cons x xs ih =>
  refine Fin.cases ?_ (fun j => ?_) i
  · have hx := (PV_OWNJ_Rows.boolean_iff x).mp (hb x (by simp))
    simp only [List.get_cons_zero,List.length_cons,Fin.val_zero,Nat.sub_zero,
     Nat.add_sub_cancel,head_bit]
    rcases hx with rfl | rfl
    · rw [hz]
      have he : equal zero one = false := by
       apply Bool.eq_false_iff.mpr
       intro h
       have hv := congrArg (fun q : Q => q.c0.a.val) ((PV_OWNJ_Rows.equal_iff _ _).mp h)
       change 0 = 1 at hv
       omega
      rw [he];rfl
    · rw [ho,show equal one one = true from (PV_OWNJ_Rows.equal_iff _ _).mpr rfl]
  · have ht := ih (fun y hy => hb y (List.mem_cons_of_mem _ hy)) j
    simpa only [List.get_cons_succ',List.length_cons,Fin.val_succ,
     show xs.length+1-1-(j.val+1) = xs.length-1-j.val from by omega,
     tail_bit x xs (xs.length-1-j.val) (by omega)] using ht

/-- Exactly the raw scanner suffix, with no equality-modulo-P substitution. -/
theorem scanner_decoded {K : Type} [Zero K] [One K] (decode : Q → K)
 (hz : decode zero = 0) (ho : decode one = 1) (point : List Q)
 (i : Fin (point.drop (width point)).length) :
 decode ((point.drop (width point)).get i) =
 if (suffix point).testBit ((point.drop (width point)).length-1-i.val) then 1 else 0 :=
 decoded_bits decode hz ho _ (PV_OWNJ_Rows.suffix_boolean point) i
#print axioms head_bit
#print axioms tail_bit
#print axioms decoded_bits
#print axioms scanner_decoded
end R1Z.PV_OWNL_Suffix
