import AspisR1ReadonlyMeta.Funs

/-! Actual SDK Pubkey equality and the extracted metadata guard. The AccountInfo
wrapper and runtime loader are outside this helper theorem. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP

namespace AspisR1ReadonlyMeta.ReadonlyMetaProof

local instance {α : Type} [DecidableEq α] {n : Usize} : DecidableEq (Array α n) :=
  inferInstanceAs (DecidableEq { l : List α // l.length = n.val })

theorem pubkey_eq_value (owner expected : solana_pubkey.Pubkey) :
    solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq owner expected =
      ok (decide (owner = expected)) := by
  have hne : ∀ x y : U8, core.cmp.PartialEqU8.ne x y ⦃ b => b ↔ x ≠ y ⦄ := by
    intro x y
    change WP.spec (ok (decide (x ≠ y))) _
    simp only [WP.spec_ok, decide_eq_true_eq]
  have hs := core.slice.cmp.PartialEqSlice.eq_homo_spec
    core.cmp.PartialEqU8 owner.to_slice expected.to_slice hne
  change WP.spec (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq owner expected)
    (fun v => v ↔ owner.to_slice = expected.to_slice) at hs
  obtain ⟨v, hv, hp⟩ := spec_imp_exists hs
  have he : owner.to_slice = expected.to_slice ↔ owner = expected := by
    constructor
    · intro h; apply Subtype.ext; exact congrArg (fun x : Slice U8 => x.val) h
    · intro h; exact congrArg Array.to_slice h
  have hp : v ↔ owner = expected := hp.trans he
  have hv' : v = decide (owner = expected) := by cases v <;> simp_all
  simpa only [hv'] using hv

theorem pubkey_ne_value (owner expected : solana_pubkey.Pubkey) :
    core.cmp.impls.PartialEqShared.ne
      solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey owner expected =
      ok (decide (owner ≠ expected)) := by
  change core.cmp.PartialEq.ne.default
    solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq owner expected = _
  simp only [core.cmp.PartialEq.ne.default, pubkey_eq_value, bind_tc_ok]
  congr 1
  simp

theorem guard_result (owner expected : solana_pubkey.Pubkey)
    (is_signer is_writable executable : Bool) :
    readonly_meta.readonly_meta_ok owner expected is_signer is_writable executable =
      if owner = expected ∧ is_signer = false ∧ is_writable = false ∧ executable = false
      then ok (core.result.Result.Ok ())
      else ok (core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData) := by
  simp only [readonly_meta.readonly_meta_ok, pubkey_ne_value, bind_tc_ok]
  by_cases h : owner = expected <;>
    cases is_signer <;> cases is_writable <;> cases executable <;> simp [h]

theorem success_iff (owner expected : solana_pubkey.Pubkey)
    (is_signer is_writable executable : Bool) :
    readonly_meta.readonly_meta_ok owner expected is_signer is_writable executable =
      ok (core.result.Result.Ok ()) ↔
      owner = expected ∧ is_signer = false ∧ is_writable = false ∧ executable = false := by
  rw [guard_result]
  split <;> simp_all

theorem invalid_account_data_iff (owner expected : solana_pubkey.Pubkey)
    (is_signer is_writable executable : Bool) :
    readonly_meta.readonly_meta_ok owner expected is_signer is_writable executable =
      ok (core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData) ↔
      ¬ (owner = expected ∧ is_signer = false ∧ is_writable = false ∧ executable = false) := by
  rw [guard_result]
  split <;> simp_all

#print axioms pubkey_eq_value
#print axioms pubkey_ne_value
#print axioms guard_result
#print axioms success_iff
#print axioms invalid_account_data_iff
end AspisR1ReadonlyMeta.ReadonlyMetaProof
