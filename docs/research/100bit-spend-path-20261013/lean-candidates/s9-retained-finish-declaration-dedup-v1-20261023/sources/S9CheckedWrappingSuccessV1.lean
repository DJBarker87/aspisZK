import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CheckedWrappingSuccessV1

theorem u64_add_success (a b out : U64) (h : (a+b : Result U64) = .ok out) :
    U64.wrapping_add a b = out := by
  have hv : out.val=a.val+b.val := by
    change UScalar.tryMk .U64 (a.val+b.val) = .ok out at h
    unfold UScalar.tryMk UScalar.tryMkOpt at h
    split at h
    · simp only [Result.ofOption] at h
      have he := congrArg UScalar.val (Result.ok.inj h)
      simpa only [UScalar.ofNatCore_val_eq] using he.symm
    · simp only [Result.ofOption] at h
      cases h
  apply UScalar.eq_of_val_eq
  rw [U64.wrapping_add_val_eq,←hv,UScalar.size]
  exact Nat.mod_eq_of_lt out.bv.isLt

theorem u64_sub_success (a b out : U64) (h : (a-b : Result U64) = .ok out) :
    U64.wrapping_sub a b = out := by
  change UScalar.sub a b = .ok out at h
  unfold UScalar.sub at h
  split at h
  · cases h
  · rename_i hnot
    have hb : b.val ≤ a.val := Nat.le_of_not_gt hnot
    have hsmall : a.val-b.val < 2^64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.bv.isLt
    have hv : out.val=a.val-b.val := by
      have he := congrArg UScalar.val (Result.ok.inj h)
      change (a.val-b.val)%2^64=out.val at he
      rw [Nat.mod_eq_of_lt hsmall] at he
      exact he.symm
    apply UScalar.eq_of_val_eq
    rw [U64.wrapping_sub_val_eq,UScalar.size]
    change (a.val+(2^64-b.val))%2^64=out.val
    have hcalc : a.val+(2^64-b.val)=(a.val-b.val)+2^64 := by
      have hbound : b.val < 2^64 := b.bv.isLt
      omega
    rw [hcalc]
    simp only [Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt hsmall]
    exact hv.symm

#print axioms u64_add_success
#print axioms u64_sub_success
end AspisR1S9CheckedWrappingSuccessV1
