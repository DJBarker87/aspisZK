-- PCVS_ item (2) helpers: frozen 4bb3b3f checkpoint_size / final_len / tag / folds (PCVS_E002, ON) against the deployed CheckpointBytes4Ops values (yDep), and QM31::ZERO (PCVS_E001).
import Aeneas
import PRVEq_WideBind_s2
import PRVEq_Tx2Deployed_q5
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option autoImplicit false
noncomputable section
namespace PCVS_Fresh2

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

end PCVS_Fresh2

namespace PCVS_Ckpt
open AspisR1 AspisR1.CheckpointBytes4Ops

def toF : AspisR1Stage2.transport.Variant → PCVS_Fresh2.transport.Variant
  | .S1 => .S1 | .S2 => .S2 | .D => .D

theorem tag_eq (v : AspisR1Stage2.transport.Variant) : PCVS_Fresh2.transport.Variant.tag (toF v) = tag v := by
  cases v <;> rfl

theorem folds_s1 : PCVS_Fresh2.transport.Variant.folds .S1 = ok 1#usize := by
  unfold PCVS_Fresh2.transport.Variant.folds PCVS_Fresh2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq
  simp

theorem folds_s2 : PCVS_Fresh2.transport.Variant.folds .S2 = ok 2#usize := by
  unfold PCVS_Fresh2.transport.Variant.folds PCVS_Fresh2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq
  first | (simp; done) | (simp [read_discriminant]; done) | decide | rfl

theorem folds_d : PCVS_Fresh2.transport.Variant.folds .D = ok 2#usize := by
  unfold PCVS_Fresh2.transport.Variant.folds PCVS_Fresh2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq
  first | (simp; done) | (simp [read_discriminant]; done) | decide | rfl

theorem final_len_eq (v : AspisR1Stage2.transport.Variant) : PCVS_Fresh2.transport.Variant.final_len (toF v) = finalLen v := by
  cases v
  · unfold PCVS_Fresh2.transport.Variant.final_len toF; rw [folds_s1]; first | rfl | simp [finalLen]
  · unfold PCVS_Fresh2.transport.Variant.final_len toF; rw [folds_s2]; first | rfl | simp [finalLen]
  · unfold PCVS_Fresh2.transport.Variant.final_len toF; rw [folds_d]; first | rfl | simp [finalLen]

theorem fixed_eq : PCVS_Fresh2.verifier.CHECKPOINT_FIXED = ok 744#usize := by
  with_unfolding_all rfl

theorem checkpoint_size_eq (v : AspisR1Stage2.transport.Variant) : PCVS_Fresh2.verifier.checkpoint_size (toF v) = checkpointSize v := by
  unfold PCVS_Fresh2.verifier.checkpoint_size checkpointSize
  rw [final_len_eq, fixed_eq]
  cases h : finalLen v with
  | ok n =>
    simp only [bind_tc_ok]
    cases hm : (16#usize * n : Result Usize) with
    | ok m => simp only [bind_tc_ok]; first | (rw [Usize.add_comm_aux]) | skip
    | fail e => rfl
    | div => rfl
  | fail e => rfl
  | div => rfl

theorem zeroK_eq (reserved : Bool) :
    (ops reserved).zeroK = ok ⟨⟨PCVS_Fresh.field.QM31.ZERO.c0.a, PCVS_Fresh.field.QM31.ZERO.c0.b⟩, ⟨PCVS_Fresh.field.QM31.ZERO.c1.a, PCVS_Fresh.field.QM31.ZERO.c1.b⟩⟩ := by
  with_unfolding_all rfl
end PCVS_Ckpt
#print axioms PCVS_Ckpt.tag_eq
#print axioms PCVS_Ckpt.final_len_eq
#print axioms PCVS_Ckpt.fixed_eq
#print axioms PCVS_Ckpt.checkpoint_size_eq
#print axioms PCVS_Ckpt.zeroK_eq
