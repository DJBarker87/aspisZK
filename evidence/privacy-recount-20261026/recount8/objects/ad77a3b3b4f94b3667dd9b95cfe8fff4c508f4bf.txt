import R1Z.PV_RDB2_FullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6CompressSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
/-- [prover_rw_success_p6::compress]: loop body 0:
    Source: 'lib.rs', lines 10:4-14:5
    Visibility: public -/
@[rust_loop_body]
def compress_loop.body
  (values : Slice aspis_core.field.M31) (lambda : aspis_core.field.QM31)
  (out : aspis_core.field.QM31) (power : aspis_core.field.QM31) (i : Std.Usize)
  :
  Result (ControlFlow (aspis_core.field.QM31 × aspis_core.field.QM31 ×
    Std.Usize) aspis_core.field.QM31)
  := do
  let i1 := Slice.len values
  if i < i1
  then
    let m ← Slice.index_usize values i
    let q ← aspis_core.field.QM31.mul_m31 power m
    let out1 ← aspis_core.field.QM31.add out q
    let power1 ← aspis_core.field.QM31.mul power lambda
    let i2 ← lift (Std.Usize.wrapping_add i 1#usize)
    ok (cont (out1, power1, i2))
  else ok (done out)

/-- [prover_rw_success_p6::compress]: loop 0:
    Source: 'lib.rs', lines 10:4-14:5
    Visibility: public -/
@[rust_loop]
def compress_loop
  (values : Slice aspis_core.field.M31) (lambda : aspis_core.field.QM31)
  (out : aspis_core.field.QM31) (power : aspis_core.field.QM31) (i : Std.Usize)
  :
  Result aspis_core.field.QM31
  := do
  loop
    (fun (out1, power1, i1) => compress_loop.body values lambda out1 power1 i1)
    (out, power, i)

/-- [prover_rw_success_p6::compress]:
    Source: 'lib.rs', lines 6:0-16:1
    Visibility: public -/
def compress
  (tag : aspis_core.field.M31) (values : Slice aspis_core.field.M31)
  (lambda : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  let c ← aspis_core.field.CM31.from_m31 tag
  let out ← aspis_core.field.QM31.from_cm31 c
  compress_loop values lambda out lambda 0#usize

end R1Z.ProverRwP6CompressSource
