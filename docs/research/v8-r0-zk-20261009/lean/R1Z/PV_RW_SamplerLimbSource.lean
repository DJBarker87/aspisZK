import R1Z.PV_OrdinaryDivBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_SamplerLimbSource
open Aeneas Aeneas.Std Result ControlFlow Error
/-- [aspis_core::field::P]
    Source: '/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/crates/aspis-core/src/field.rs', lines 19:0-19:16
    Name pattern: [aspis_core::field::P]
    Visibility: public -/
@[global_simps, irreducible, rust_const "aspis_core::field::P"]
def aspis_core.field.P : Std.U32 := 2147483647#u32

/-- [pv_rw_step::sampler_step::shipped_limb]:
    Source: 'sampler_step.rs', lines 3:0-8:1
    Visibility: public -/
def sampler_step.shipped_limb
  (limb : Std.U32) (remainder : Std.U64) : Result (Std.U32 × Std.U64) := do
  let i ← lift (Std.U64.wrapping_shl remainder 32#u32)
  let i1 ← lift (core.convert.num.FromU64U32.from limb)
  let dividend ← lift (i ||| i1)
  let i2 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
  let i3 ← dividend / i2
  let limb1 ← lift (UScalar.cast .U32 i3)
  let i4 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
  let remainder1 ← dividend % i4
  ok (limb1, remainder1)


def owned (limb : U32) (remainder : U64) : Result (U32 × U64) := do
  let dividend := U64.wrapping_shl remainder 32#u32 |||
    core.convert.num.FromU64U32.from limb
  let divisor := core.convert.num.FromU64U32.from PV_OrdinarySource.aspis_core.field.P
  let quotient ← dividend / divisor
  let next ← dividend % divisor
  ok (UScalar.cast .U32 quotient,next)

theorem limb (word : U32) (remainder : U64) :
    sampler_step.shipped_limb word remainder = owned word remainder := by
  simp only [sampler_step.shipped_limb,owned,aspis_core.field.P,
    PV_OrdinarySource.aspis_core.field.P,lift,bind_tc_ok]
#print axioms limb
end R1Z.PV_RW_SamplerLimbSource
