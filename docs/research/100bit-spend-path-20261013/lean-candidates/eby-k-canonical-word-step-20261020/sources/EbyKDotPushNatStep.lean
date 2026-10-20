import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Aeneas

set_option autoImplicit false

namespace AspisR1EbyKDotPushNatStep
open Aeneas.Std

def modulus : Nat := 2 ^ 31 - 1
def limbBase : Nat := 2 ^ 31

/-- The arithmetic model of the Rust expression `(raw & P) + (raw >> 31)`.
The bit-mask/shift-to-mod/div correspondence is kept as a source adapter
obligation; all bounds and residue facts below concern this exact Nat model. -/
def foldedRaw (raw : Nat) : Nat := raw % limbBase + raw / limbBase

/-- Model of `u64::wrapping_add`, interpreted in Nat. -/
def wrappingAdd (x y : Nat) : Nat := (x + y) % (2 ^ 64)

theorem modulus_succ : modulus + 1 = limbBase := by
  norm_num [modulus, limbBase]

theorem foldedRaw_preserves_mod (raw : Nat) :
    foldedRaw raw % modulus = raw % modulus := by
  have hdiv : raw % limbBase + limbBase * (raw / limbBase) = raw :=
    Nat.mod_add_div _ _
  have hlimb : limbBase = 2147483648 := by norm_num [limbBase]
  have hmodulus : modulus = 2147483647 := by norm_num [modulus]
  have hrepr : raw = foldedRaw raw + modulus * (raw / limbBase) := by
    dsimp [foldedRaw] at *
    rw [hlimb] at hdiv ⊢
    rw [hmodulus]
    omega
  calc
    foldedRaw raw % modulus =
        (foldedRaw raw + modulus * (raw / limbBase)) % modulus :=
      (Nat.add_mul_mod_self_left (foldedRaw raw) modulus (raw / limbBase)).symm
    _ = raw % modulus := by rw [← hrepr]

theorem foldedRaw_lt_two34 {raw : Nat} (hraw : raw < 2 ^ 64) :
    foldedRaw raw < 2 ^ 34 := by
  have hmod : raw % limbBase < limbBase :=
    Nat.mod_lt _ (by norm_num [limbBase])
  have hlimb : limbBase = 2 ^ 31 := by norm_num [limbBase]
  have hdiv : raw / limbBase < 2 ^ 33 := by
    apply Nat.div_lt_iff_lt_mul (by norm_num [limbBase]) |>.2
    calc
      raw < 2 ^ 64 := hraw
      _ = (2 ^ 33) * limbBase := by norm_num [limbBase, pow_add]
  rw [hlimb] at hmod hdiv
  unfold foldedRaw
  rw [hlimb]
  omega

theorem wrappingAdd_of_no_wrap {x y : Nat} (hxy : x + y < 2 ^ 64) :
    wrappingAdd x y = x + y := by
  exact Nat.mod_eq_of_lt hxy

/-- The actual Aeneas U64 wrapping primitive agrees with ordinary addition
under the same no-wrap bound. This is independent of the untranslated Rust
loop and is intended to compose with `coordinate_step`. -/
theorem u64_wrappingAdd_of_no_wrap (x y : U64)
    (hxy : x.val + y.val < 2 ^ 64) :
    (U64.wrapping_add x y).val = x.val + y.val := by
  change (x.bv + y.bv).toNat = x.bv.toNat + y.bv.toNat
  rw [BitVec.toNat_add]
  change x.bv.toNat + y.bv.toNat < 2 ^ 64 at hxy
  exact Nat.mod_eq_of_lt hxy

/-- One coordinate of `Dot::push`: given the accumulator's prior bound and a
64-bit raw coordinate, the exact fold fits and `wrapping_add` is ordinary
addition. Its field residue is the prior residue plus the raw coordinate.
This is the arithmetic step only; generated-body/bit-mask correspondence and
the premise that the concrete raw formula is below 2^64 remain separate. -/
theorem coordinate_step {acc raw : Nat}
    (hacc : acc < 2 ^ 46) (hraw : raw < 2 ^ 64) :
    wrappingAdd acc (foldedRaw raw) = acc + foldedRaw raw ∧
    acc + foldedRaw raw < 2 ^ 64 ∧
    (acc + foldedRaw raw) % modulus = (acc + raw) % modulus ∧
    foldedRaw raw < 2 ^ 34 := by
  have hfold := foldedRaw_lt_two34 hraw
  have hsum : acc + foldedRaw raw < 2 ^ 64 := by omega
  refine ⟨wrappingAdd_of_no_wrap hsum, hsum, ?_, hfold⟩
  calc
    (acc + foldedRaw raw) % modulus =
        (acc % modulus + foldedRaw raw % modulus) % modulus :=
      (Nat.add_mod _ _ _)
    _ = (acc % modulus + raw % modulus) % modulus := by
      rw [foldedRaw_preserves_mod]
    _ = (acc + raw) % modulus := (Nat.add_mod _ _ _).symm

/-- Actual U64 wrapping-add step after reifying the Nat fold as a U64 word.
This isolates the exact update operation used by Dot::push; connecting the
concrete mask/shift expression to `foldedRawU64` is discharged separately by
the accepted flush-primitive bridge. -/
def foldedRawU64 (raw : U64) (hraw : raw.val < 2 ^ 64) : U64 :=
  UScalar.ofNatCore (foldedRaw raw.val) (by
    have hf := foldedRaw_lt_two34 hraw
    rw [UScalarTy.U64_numBits_eq]
    omega)

theorem foldedRawU64_val (raw : U64) (hraw : raw.val < 2 ^ 64) :
    (foldedRawU64 raw hraw).val = foldedRaw raw.val := rfl

theorem u64_coordinate_step {acc raw : U64}
    (hacc : acc.val < 2 ^ 46) (hraw : raw.val < 2 ^ 64) :
    (U64.wrapping_add acc (foldedRawU64 raw hraw)).val =
      acc.val + foldedRaw raw.val ∧
    acc.val + foldedRaw raw.val < 2 ^ 64 ∧
    (acc.val + foldedRaw raw.val) % modulus =
      (acc.val + raw.val) % modulus := by
  have hfold := foldedRaw_lt_two34 hraw
  have hsum : acc.val + (foldedRawU64 raw hraw).val < 2 ^ 64 := by
    rw [foldedRawU64_val]
    omega
  have hwrap := u64_wrappingAdd_of_no_wrap acc (foldedRawU64 raw hraw) hsum
  rw [foldedRawU64_val] at hsum hwrap
  have hres := (coordinate_step hacc hraw).2.2.1
  exact ⟨hwrap, hsum, hres⟩

#print axioms foldedRaw_preserves_mod
#print axioms foldedRaw_lt_two34
#print axioms wrappingAdd_of_no_wrap
#print axioms u64_wrappingAdd_of_no_wrap
#print axioms coordinate_step
#print axioms u64_coordinate_step

end AspisR1EbyKDotPushNatStep
