import AspisR1WithdrawalValidation.Funs

/-! Amount consequence of the actual extracted payment validator.
Successful helper execution is the premise. This does not assert that an
arbitrary verifier caller reached it, nor merge the 4.31/4.32 proof kernels. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1WithdrawalValidation.Amount431
open pool_v1.payment_relation

abbrev Public := PoolV1WithdrawalPublicV1

theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem valueLimit_eq : VALUE_LIMIT = ok 1073741824#u32 := by
  unfold VALUE_LIMIT
  rfl

/-- Nonzero and the payment range follow from generated success; field
canonicality alone would not give either this positivity or the upper bound. -/
theorem success_amount_guard (p : Public)
    (h : validate_pool_v1_withdrawal_public_v1 p = ok (.Ok ())) :
    0 < p.amount.val ∧ p.amount.val < 2 ^ 30 := by
  simp only [validate_pool_v1_withdrawal_public_v1, withdrawal_common, bind_tc_ok] at h
  obtain ⟨r, _, h⟩ := bind_success _ _ _ h
  cases r with
  | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame] at h
  | Ok u =>
      cases u
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
      by_cases hz : p.amount = 0#u32
      · simp only [hz, if_true] at h
        cases h
      · simp only [hz, if_false, valueLimit_eq, bind_tc_ok] at h
        by_cases hbig : 1073741824#u32 ≤ p.amount
        · simp only [if_pos hbig] at h
          cases h
        · constructor
          · have hn : p.amount.val ≠ 0 := by
              intro heq
              exact hz (UScalar.eq_of_val_eq heq)
            omega
          · change ¬ 1073741824 ≤ p.amount.val at hbig
            exact Nat.lt_of_not_ge hbig

theorem success_nonzero (p : Public)
    (h : validate_pool_v1_withdrawal_public_v1 p = ok (.Ok ())) :
    p.amount.val ≠ 0 := by
  exact Nat.ne_of_gt (success_amount_guard p h).1

/-- Exact result for the fixed eight-coordinate array; no iteration axiom. -/
theorem digest_make (a0 a1 a2 a3 a4 a5 a6 a7 : U32) :
    digest_is_canonical (Array.make 8#usize [a0, a1, a2, a3, a4, a5, a6, a7]) =
      ok (decide (a0.val < 2147483647 ∧ a1.val < 2147483647 ∧
        a2.val < 2147483647 ∧ a3.val < 2147483647 ∧
        a4.val < 2147483647 ∧ a5.val < 2147483647 ∧
        a6.val < 2147483647 ∧ a7.val < 2147483647)) := by
  simp only [digest_is_canonical, Array.index_usize, Array.make]
  by_cases h0 : a0.val < 2147483647
  case neg => simp [h0, aspis_core.field.P]
  by_cases h1 : a1.val < 2147483647
  case neg => simp [h0, h1, aspis_core.field.P]
  by_cases h2 : a2.val < 2147483647
  case neg => simp [h0, h1, h2, aspis_core.field.P]
  by_cases h3 : a3.val < 2147483647
  case neg => simp [h0, h1, h2, h3, aspis_core.field.P]
  by_cases h4 : a4.val < 2147483647
  case neg => simp [h0, h1, h2, h3, h4, aspis_core.field.P]
  by_cases h5 : a5.val < 2147483647
  case neg => simp [h0, h1, h2, h3, h4, h5, aspis_core.field.P]
  by_cases h6 : a6.val < 2147483647
  case neg => simp [h0, h1, h2, h3, h4, h5, h6, aspis_core.field.P]
  simp [h0, h1, h2, h3, h4, h5, h6, aspis_core.field.P]

/-- Every coordinate of an arbitrary fixed-width digest is canonical exactly
when the actual generated predicate returns true. -/
theorem digest_success_iff (d : Array aspis_core.field.M31 8#usize) :
    digest_is_canonical d = ok true ↔
      ∀ a ∈ d.val, a.val < 2147483647 := by
  rcases d with ⟨xs, hlen⟩
  change xs.length = 8 at hlen
  cases xs with
  | nil => simp at hlen
  | cons a0 xs =>
      cases xs with
      | nil => simp at hlen
      | cons a1 xs =>
          cases xs with
          | nil => simp at hlen
          | cons a2 xs =>
              cases xs with
              | nil => simp at hlen
              | cons a3 xs =>
                  cases xs with
                  | nil => simp at hlen
                  | cons a4 xs =>
                      cases xs with
                      | nil => simp at hlen
                      | cons a5 xs =>
                          cases xs with
                          | nil => simp at hlen
                          | cons a6 xs =>
                              cases xs with
                              | nil => simp at hlen
                              | cons a7 xs =>
                                  have hz : xs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
                                  subst xs
                                  change digest_is_canonical (Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7]) = ok true ↔ _
                                  rw [digest_make]
                                  simp

#print axioms pool_v1.payment_relation.digest_is_canonical
#print axioms pool_v1.payment_relation.validate_common
#print axioms pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1
#print axioms valueLimit_eq
#print axioms success_amount_guard
#print axioms success_nonzero
#print axioms digest_make
#print axioms digest_success_iff
end AspisR1WithdrawalValidation.Amount431
