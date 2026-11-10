import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
noncomputable section
namespace T0
/-- [aspis_r1_cost_probe::transport::Variant]
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 3:0-3:30
    Visibility: public -/
@[discriminant isize]
inductive transport.Variant where
| S1 : transport.Variant
| S2 : transport.Variant
| D : transport.Variant

/-- [aspis_r1_cost_probe::transport::{impl core::cmp::PartialEq<aspis_r1_cost_probe::transport::Variant> for aspis_r1_cost_probe::transport::Variant}::eq]:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 2:26-2:35
    Visibility: public -/
def transport.Variant.Insts.CoreCmpPartialEqVariant.eq
  (self : transport.Variant) (other : transport.Variant) : Result Bool := do
  let self1 := read_discriminant self
  let other1 := read_discriminant other
  ok (self1 = other1)

/-- [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::tag]:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 6:4-6:80
    Visibility: public -/
def transport.Variant.tag (self : transport.Variant) : Result Std.U8 := do
  match self with
  | transport.Variant.S1 => ok 1#u8
  | transport.Variant.S2 => ok 2#u8
  | transport.Variant.D => ok 3#u8

/-- [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::folds]:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 8:4-8:72
    Visibility: public -/
def transport.Variant.folds (self : transport.Variant) : Result Std.Usize := do
  let b ←
    transport.Variant.Insts.CoreCmpPartialEqVariant.eq self
      transport.Variant.S1
  if b
  then ok 1#usize
  else ok 2#usize

/-- [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::final_len]:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 9:4-9:64
    Visibility: public -/
def transport.Variant.final_len
  (self : transport.Variant) : Result Std.Usize := do
  let i ← transport.Variant.folds self
  let i1 ← 2#usize * i
  1024#usize >>> i1

/-- [aspis_r1_cost_probe::verifier::CHECKPOINT_FIXED]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 18:0-18:73
    Visibility: public -/
@[global_simps, irreducible]
def verifier.CHECKPOINT_FIXED : Result Std.Usize := do
  let i ← 32#usize * 3#usize
  let i1 ← 16#usize + i
  let i2 ← i1 + 64#usize
  let i3 ← 32#usize * 4#usize
  let i4 ← i2 + i3
  let i5 ← i4 + 16#usize
  let i6 ← i5 + 88#usize
  let i7 ← i6 + 160#usize
  let i8 ← i7 + 64#usize
  let i9 ← 32#usize * 2#usize
  let i10 ← i8 + i9
  let i11 ← i10 + 16#usize
  i11 + 32#usize

/-- [aspis_r1_cost_probe::verifier::checkpoint_size]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 32:0-32:76
    Visibility: public -/
def verifier.checkpoint_size (v : transport.Variant) : Result Std.Usize := do
  let i ← transport.Variant.final_len v
  let i1 ← 16#usize * i
  let i2 ← verifier.CHECKPOINT_FIXED
  i2 + i1



#print transport.Variant.read_discriminant
theorem v1 : (32#usize).val = 32 := by simp
theorem v2 : (32#usize).val = 32 := by scalar_tac
theorem v3 : (32#usize).val = 32 := by rfl
theorem d1 : (decide (transport.Variant.S2.read_discriminant = transport.Variant.S1.read_discriminant)) = false := by decide
theorem d2 : (decide (transport.Variant.S2.read_discriminant = transport.Variant.S1.read_discriminant)) = false := by
  simp [transport.Variant.read_discriminant]
theorem d3 : (decide (transport.Variant.S2.read_discriminant = transport.Variant.S1.read_discriminant)) = false := by
  rfl
theorem d4 : (decide (transport.Variant.S2.read_discriminant = transport.Variant.S1.read_discriminant)) = false := by
  unfold transport.Variant.read_discriminant
  simp
theorem usz_mul (x y z : Std.Usize) (h : x.val * y.val = z.val) : (x * y : Result Std.Usize) = ok z := by
  have := Std.Usize.mul_spec (x := x) (y := y) (by scalar_tac)
  obtain ⟨w, hw, hwv⟩ := spec_imp_exists this
  rw [hw]
  congr 1
  apply UScalar.eq_of_val_eq
  omega
theorem usz_add (x y z : Std.Usize) (h : x.val + y.val = z.val) : (x + y : Result Std.Usize) = ok z := by
  have := Std.Usize.add_spec (x := x) (y := y) (by scalar_tac)
  obtain ⟨w, hw, hwv⟩ := spec_imp_exists this
  rw [hw]
  congr 1
  apply UScalar.eq_of_val_eq
  omega
theorem usz_shr (x i z : Std.Usize) (hi : i.val < 32) (h : x.val / 2 ^ i.val = z.val) :
    (x >>> i : Result Std.Usize) = ok z := by
  show UScalar.shiftRight_UScalar x i = _
  unfold UScalar.shiftRight_UScalar UScalar.shiftRight
  have hn : i.val < UScalarTy.Usize.numBits := by
    rcases System.Platform.numBits_eq with hb | hb <;> simp [UScalarTy.numBits, hb] <;> omega
  rw [if_pos hn]
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [UScalar.val, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact h
theorem t1e : (32#usize * 3#usize : Result Std.Usize) = ok 96#usize := by
  apply usz_mul <;> simp
theorem t1f : (32#usize * 3#usize : Result Std.Usize) = ok 96#usize := by
  apply usz_mul; scalar_tac
theorem t1g : verifier.checkpoint_size transport.Variant.S2 = ok 1768#usize := by
  unfold verifier.checkpoint_size transport.Variant.final_len transport.Variant.folds transport.Variant.Insts.CoreCmpPartialEqVariant.eq verifier.CHECKPOINT_FIXED
  have hd : (decide (transport.Variant.S2.read_discriminant = transport.Variant.S1.read_discriminant)) = false := by
    first | decide | rfl | (simp [transport.Variant.read_discriminant])
  simp only [hd]
  rw [show (if (false = true) then (ok 1#usize : Result Std.Usize) else ok 2#usize) = ok 2#usize from rfl]

end T0
