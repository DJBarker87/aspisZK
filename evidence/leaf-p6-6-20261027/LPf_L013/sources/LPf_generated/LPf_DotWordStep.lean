import LPf_ReductionWord
set_option autoImplicit false
namespace AspisR1.LPf_DotWordStep
open Aeneas Aeneas.Std Result

def bound : Nat := 10737418238

theorem fold_bound (raw : U64) : (FIo_ReduceBounds.fold raw).val ≤ bound := by
  rw [LPf_ReductionWord.fold_value]
  have h : raw.val < 18446744073709551616 := by scalar_tac
  unfold LPe_MersenneReduction.fold bound
  omega

/-- Actual per-coordinate wrapping addition is ordinary addition for every
reached count below the public4096 term cap, on arbitrary raw u64 inputs. -/
theorem value (sum raw : U64) (n : Nat) (hn : n < 4096)
    (hs : sum.val ≤ n*bound) :
    (U64.wrapping_add sum (FIo_ReduceBounds.fold raw)).val =
      sum.val + (FIo_ReduceBounds.fold raw).val ∧
    (U64.wrapping_add sum (FIo_ReduceBounds.fold raw)).val ≤ (n+1)*bound := by
  have hf := fold_bound raw
  have small : sum.val + (FIo_ReduceBounds.fold raw).val < UScalar.size .U64 := by
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits]
    unfold bound at *
    omega
  rw [U64.wrapping_add_val_eq,Nat.mod_eq_of_lt small]
  constructor
  · rfl
  · simpa only [Nat.add_mul,Nat.one_mul] using Nat.add_le_add hs hf

/-- Mathematical reduction of that exact word update: each raw representative
contributes its residue, including nonzero and maximal raw words. -/
theorem reduced (sum raw : U64) (n : Nat) (hn : n < 4096)
    (hs : sum.val ≤ n*bound) : ∃ z,
    FIo_Native.fast_pairing.canonical.reduce
      (U64.wrapping_add sum (FIo_ReduceBounds.fold raw)) = ok z ∧
    z.val = (sum.val + raw.val) % 2147483647 ∧ z.val < 2147483647 := by
  obtain ⟨z,run,v,c⟩ := LPf_ReductionWord.native_reduce
    (U64.wrapping_add sum (FIo_ReduceBounds.fold raw))
  refine ⟨z,run,?_,c⟩
  rw [(value sum raw n hn hs).1,LPf_ReductionWord.fold_value] at v
  simpa only [Nat.add_mod,LPe_MersenneReduction.fold_mod] using v

#print axioms fold_bound
#print axioms value
#print axioms reduced
end AspisR1.LPf_DotWordStep
