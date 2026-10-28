import R1Z.PV_RW_NativeForSource
import R1Z.PV_RW_CompressEmission
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_IteratorStateSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Iter := core.slice.iter.Iter aspis_core.field.M31
abbrev Q := aspis_core.field.QM31
/-- [pv_rw_step::iterator_state_step::iterator_state_step]:
    Source: 'iterator_state_step.rs', lines 4:0-13:1
    Visibility: public -/
def iterator_state_step.iterator_state_step
  (iterator : core.slice.iter.Iter aspis_core.field.M31)
  (compressed : aspis_core.field.QM31) (power : aspis_core.field.QM31)
  (lambda : aspis_core.field.QM31) :
  Result (Bool × (core.slice.iter.Iter aspis_core.field.M31) ×
    aspis_core.field.QM31 × aspis_core.field.QM31)
  := do
  let (o, iterator1) ← core.slice.iter.IteratorSliceIter.next iterator
  match o with
  | none => ok (false, iterator1, compressed, power)
  | some value =>
    let q ← aspis_core.field.QM31.mul_m31 power value
    let compressed1 ← aspis_core.field.QM31.add compressed q
    let power1 ← aspis_core.field.QM31.mul power lambda
    ok (true, iterator1, compressed1, power1)


def body (lambda : Q) (iterator : Iter) (state : Q × Q) :
    Result (ControlFlow (Iter × (Q × Q)) (Q × Q)) := do
  let (live,next,out,power) ← iterator_state_step.iterator_state_step iterator state.1 state.2 lambda
  if live then ok (cont (next,(out,power))) else ok (done (out,power))

theorem control (lambda : Q) (iterator : Iter) (state : Q × Q) :
    body lambda iterator state=PV_RW_NativeForSource.body (fun value acc =>
      PV_RW_CompressEmission.generated.shipped_step acc.1 acc.2 value lambda) iterator state := by
  unfold body iterator_state_step.iterator_state_step PV_RW_NativeForSource.body
  rw [PV_RW_IteratorSource.exact]
  cases h : core.slice.iter.IteratorSliceIter.next iterator with
  | fail error => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨head,next⟩
    cases head with
    | none => rfl
    | some value =>
      simp [bind_tc_ok,PV_RW_CompressEmission.generated.shipped_step,bind_assoc_eq]
#print axioms control
end R1Z.PV_RW_IteratorStateSource
