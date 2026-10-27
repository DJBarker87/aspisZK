import XRk_DotModel
open Aeneas Aeneas.Std Result ControlFlow Error
open XRk_Release XRk_FieldExternal
/- Algebraic field model. P6 with the fixed source inverse chain OPEN. -/
def XRk_qpow (x : aspis_core.field.QM31) : Nat → Result aspis_core.field.QM31
  | 0 => ok qone
  | n+1 => do
    let y ← XRk_qpow x (n/2)
    let z ← aspis_core.field.QM31.mul y y
    if n%2 = 0 then aspis_core.field.QM31.mul z x else ok z
termination_by n => n
/- circle.rs:30-69: singularity first, then CM31 rejection. This is a
   transparent mathematical external, not a source inverse/P6 theorem. -/
def aspis_core.circle.secure_ood_circle_point_from_parameter (t : aspis_core.field.QM31) :
    Result (core.result.Result aspis_core.circle.SecureCirclePoint aspis_core.circle.CirclePointError) := do
  let square ← aspis_core.field.QM31.mul t t
  let den ← aspis_core.field.QM31.add qone square
  if qeq den qzero then ok (.Err .SingularParameter) else do
    let inverse ← XRk_qpow den (2147483647^4-2)
    let numerator ← XRk_Field.field.QM31.sub qone square
    let x ← aspis_core.field.QM31.mul numerator inverse
    let twice ← aspis_core.field.QM31.add t t
    let y ← aspis_core.field.QM31.mul twice inverse
    if (t.c1.a == 0#u32 && t.c1.b == 0#u32) then ok (.Err .ParameterInCm31Subfield)
    else ok (.Ok ⟨x,y⟩)
/- XRg_fallback_reference: row chooses t=u or t=1+u; same fall-through
   default if the rational map rejects. Capture/move/borrow/P6 OPEN. -/
def sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once
    (row : sampler.circle_sample.closure) (_ : aspis_core.circle.CirclePointError) :
    Result aspis_core.circle.SecureCirclePoint := do
  let t : aspis_core.field.QM31 := match row with
    | .First => ⟨⟨0#u32,0#u32⟩,⟨1#u32,0#u32⟩⟩
    | .Second => ⟨⟨1#u32,0#u32⟩,⟨1#u32,0#u32⟩⟩
  let point ← aspis_core.circle.secure_ood_circle_point_from_parameter t
  match point with
  | .Ok p => ok p
  | .Err _ => ok ⟨qone,qzero⟩
