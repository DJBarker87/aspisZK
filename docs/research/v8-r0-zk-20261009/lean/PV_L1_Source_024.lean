import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_024
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize))
  (z1 : aspis_core.r0.domain.Point aspis_core.field.wide_exact.WideExact) :
  Logged (alloc.vec.Vec Std.U8)
  := do
  let _ ← observe .opening 0 (ok ())
  let i := Slice.len coefficients
  let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_mul 32#usize i)
  let bytes := alloc.vec.Vec.with_capacity Std.U8 i1
  prover.opening_claim_bytes_loop coefficients z1 bytes 0#usize

theorem complete_result
  (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize))
  (z1 : aspis_core.r0.domain.Point aspis_core.field.wide_exact.WideExact) :
  erase (produce coefficients z1) = prover.opening_claim_bytes coefficients z1 := by
  unfold produce prover.opening_claim_bytes
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
#print axioms complete_result
end PV_L1_Source_024
