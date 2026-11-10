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


theorem t1a : verifier.checkpoint_size transport.Variant.S2 = ok 1768#usize := by
  unfold verifier.checkpoint_size transport.Variant.final_len transport.Variant.folds transport.Variant.Insts.CoreCmpPartialEqVariant.eq verifier.CHECKPOINT_FIXED
  rfl
theorem t1b : verifier.checkpoint_size transport.Variant.S2 = ok 1768#usize := by
  unfold verifier.checkpoint_size transport.Variant.final_len transport.Variant.folds transport.Variant.Insts.CoreCmpPartialEqVariant.eq verifier.CHECKPOINT_FIXED
  decide
theorem t1c : verifier.checkpoint_size transport.Variant.S2 = ok 1768#usize := by
  unfold verifier.checkpoint_size transport.Variant.final_len transport.Variant.folds transport.Variant.Insts.CoreCmpPartialEqVariant.eq verifier.CHECKPOINT_FIXED
  cases System.Platform.numBits_eq <;> simp [*]
theorem t1d : verifier.checkpoint_size transport.Variant.S2 = ok 1768#usize := by
  unfold verifier.checkpoint_size transport.Variant.final_len transport.Variant.folds transport.Variant.Insts.CoreCmpPartialEqVariant.eq verifier.CHECKPOINT_FIXED
  simp
theorem t2a : UScalar.cast .U8 (10#usize) = 10#u8 := by rfl
theorem t2b : UScalar.cast .U8 (10#usize) = 10#u8 := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq]
  simp
theorem t2c : UScalar.cast .U8 (10#usize) = 10#u8 := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq]
  cases System.Platform.numBits_eq <;> simp [*]
theorem t3a {T : Type} (z0 z1 : T) (h : [z0, z1].length = (2#usize).val := by scalar_tac) :
    Array.index_usize (⟨[z0, z1], by scalar_tac⟩ : Array T 2#usize) 0#usize = ok z0 := by rfl
theorem t3b {T : Type} (z0 z1 : T) :
    Array.index_usize (⟨[z0, z1], by scalar_tac⟩ : Array T 2#usize) 0#usize = ok z0 := by
  simp [Array.index_usize]
theorem t3c {T : Type} (z0 z1 : T) :
    Array.index_usize (⟨[z0, z1], by scalar_tac⟩ : Array T 2#usize) 1#usize = ok z1 := by
  simp [Array.index_usize]
theorem t3d {T : Type} (z0 z1 : T) :
    Array.index_usize (⟨[z0, z1], by scalar_tac⟩ : Array T 2#usize) 1#usize = ok z1 := by
  cases System.Platform.numBits_eq <;> simp [Array.index_usize, *]
theorem t4 : alloc.vec.Vec.with_capacity Std.U8 1768#usize = alloc.vec.Vec.with_capacity Std.U8 1768#usize := rfl
theorem t5 {T : Type} (n m : Usize) : alloc.vec.Vec.with_capacity T n = alloc.vec.Vec.with_capacity T m := by rfl
theorem t6 : (Std.massert (64#usize = 64#usize)) = ok () := by simp [Std.massert]
theorem t7 : (Std.massert (64#usize = 64#usize)) = ok () := by rfl

end T0
