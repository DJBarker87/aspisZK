import R1Z.PV_OWNI_Scanner
set_option autoImplicit false
namespace R1Z.PV_OWNJ_Rows
open PV_OWNI_RawOps PV_OWNI_Scanner

theorem equal_iff (a b : Q) : equal a b = true ↔ a = b := by
  simp only [equal, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨h0,h1⟩,h2⟩,h3⟩
    cases a with | mk ac0 ac1 =>
     cases b with | mk bc0 bc1 =>
      cases ac0; cases ac1; cases bc0; cases bc1
      dsimp only at h0 h1 h2 h3
      cases Aeneas.Std.UScalar.eq_of_val_eq h0
      cases Aeneas.Std.UScalar.eq_of_val_eq h1
      cases Aeneas.Std.UScalar.eq_of_val_eq h2
      cases Aeneas.Std.UScalar.eq_of_val_eq h3
      rfl
  · intro h; subst b; simp

theorem boolean_iff (a : Q) : boolean a = true ↔ a = zero ∨ a = one := by
  simp only [boolean, Bool.or_eq_true, equal_iff]

/-- Native row shift/OR is uniquely decoded by quotient and remainder. -/
theorem row_decode (pref trailing suffix : Nat) (hs : suffix < 2^trailing) :
 let row := PV_RDB2D_SparseAddress.row pref trailing suffix
 row / 2^trailing = pref ∧ row % 2^trailing = suffix := by
  constructor
  · exact PV_RDB2D_SparseAddress.quotient trailing suffix pref hs
  · simp only [PV_RDB2D_SparseAddress.row,Nat.add_mod,Nat.mul_mod_right,
      Nat.zero_add,Nat.mod_eq_of_lt hs]

theorem takeWhile_take_length {A : Type} (p : A → Bool) (xs : List A) :
 xs.take (xs.takeWhile p).length = xs.takeWhile p := by
 induction xs with
 | nil => rfl
 | cons x xs ih =>
  cases h:p x <;> simp only [List.takeWhile_cons,h,Bool.false_eq_true,
   if_false,if_true,List.length_nil,List.take_zero,List.length_cons,List.take_succ_cons,ih]

theorem takeWhile_mem {A : Type} (p : A → Bool) (xs : List A) :
 ∀ x ∈ xs.takeWhile p, p x = true := by
 induction xs with
 | nil => simp
 | cons x xs ih =>
  cases h:p x <;> simp only [List.takeWhile_cons,h,Bool.false_eq_true,if_false,if_true]
  · simp
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h
    · exact ih y hy

/-- The scanner drops exactly the Boolean suffix, in its original order. -/
theorem suffix_boolean (point : List Q) :
 ∀ x ∈ point.drop (width point), boolean x = true := by
 have hb := PV_RDB2D_SparseShape.trailing_bound boolean point
 have hr : (point.drop (width point)).reverse = point.reverse.takeWhile boolean := by
  rw [List.reverse_drop]
  unfold width PV_RDB2D_SparseShape.prefixLen
  have hn : point.length - (point.length - PV_RDB2D_SparseShape.trailing boolean point) =
    PV_RDB2D_SparseShape.trailing boolean point := by omega
  rw [hn]
  exact takeWhile_take_length boolean point.reverse
 intro x hx
 have hm : x ∈ point.reverse.takeWhile boolean := by
  rw [← hr]; exact List.mem_reverse.mpr hx
 exact takeWhile_mem boolean point.reverse x hm

#print axioms equal_iff
#print axioms boolean_iff
#print axioms row_decode
#print axioms takeWhile_take_length
#print axioms takeWhile_mem
#print axioms suffix_boolean
end R1Z.PV_OWNJ_Rows
