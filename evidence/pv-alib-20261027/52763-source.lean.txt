import R1Z.PV_AL_CircleOwnedFuns
import R1Z.PV_AL_CircleControl
open Aeneas Aeneas.Std Result
namespace R1Z.PV_AL_CircleNative
open PV_AL_CircleOwned
set_option autoImplicit false

/-- Literal frozen point construction, shared arithmetic calls in source order. -/
def makePoint (parameter square inverse : aspis_core.field.QM31) :
    Result aspis_core.circle.SecureCirclePoint := do
  let q1 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE square
  let q2 ← aspis_core.field.QM31.mul q1 inverse
  let q3 ← aspis_core.field.QM31.add parameter parameter
  let q4 ← aspis_core.field.QM31.mul q3 inverse
  ok {x:=q2,y:=q4}

/-- Structural interpretation of the two frozen circle.rs helpers: ok_or/?,
then OOD policy after constructing the point. It does not call map_parameter. -/
def nativeMap (parameter : aspis_core.field.QM31) :
    Result (core.result.Result aspis_core.circle.SecureCirclePoint aspis_core.circle.CirclePointError) := do
  let square ← aspis_core.field.QM31.square parameter
  let denominator ← aspis_core.field.QM31.add aspis_core.field.QM31.ONE square
  PV_AL_CircleControl.nativeOod
    (PV_AL_CircleControl.nativeInner (aspis_core.field.QM31.try_inv denominator)
      (makePoint parameter square) .SingularParameter)
    (aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq parameter.c1 aspis_core.field.CM31.ZERO)
    .ParameterInCm31Subfield

/-- Unbounded complete-Result control transport, sharing every field operation;
no field equality, success, or native/reference equation is assumed. -/
theorem map_source (parameter : aspis_core.field.QM31) :
    nativeMap parameter=PV_AL_CircleOwned.map_parameter parameter := by
  simp only [nativeMap,PV_AL_CircleControl.native_owned,PV_AL_CircleControl.owned,
    makePoint,bind_assoc_eq,bind_tc_ok,PV_AL_CircleOwned.map_parameter]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro square _
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro denominator _
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro inverse _
  cases inverse with
  | none => rfl
  | some i =>
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro numerator _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro x _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro doubled _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro y _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro bad _
    cases bad <;> simp

def nativeFallback (sample : Usize) : Result aspis_core.circle.SecureCirclePoint := do
  let i ← sample % 2#usize
  let parameter ← Array.index_usize FALLBACK i
  let r ← nativeMap parameter
  match r with
  | .Ok point => ok point
  | .Err _ => ok {x:=aspis_core.field.QM31.ONE,y:=aspis_core.field.QM31.ZERO}

theorem fallback_source (sample : Usize) :
    nativeFallback sample=PV_AL_CircleOwned.fallback sample := by
  simp only [nativeFallback,PV_AL_CircleOwned.fallback,map_source]
  rfl

/-- Frozen sampler.rs unwrap_or_else wrapper, interpreted structurally over the
same extracted native sampler, circle arithmetic and fallback constants. -/
def nativeCircle (block : Array U8 32#usize) (row : aspis_core.r0_transcript.CircleRow) :
    Result aspis_core.circle.SecureCirclePoint := do
  let parameter ← shipped_sampler.qm31_sample block
  let r ← nativeMap parameter
  PV_AL_CircleControl.unwrapOrElse r (fun _ => nativeFallback
    (match row with | .First => 0#usize | .Second => 1#usize))

theorem source_reference (block : Array U8 32#usize) (row : aspis_core.r0_transcript.CircleRow) :
    nativeCircle block row=PV_AL_CircleOwned.circle_owned block row := by
  simp only [nativeCircle,PV_AL_CircleOwned.circle_owned,map_source]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro parameter _
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro r _
  cases r with
  | Ok point => rfl
  | Err e => cases row <;> simp only [PV_AL_CircleControl.unwrapOrElse,fallback_source]

#print axioms makePoint
#print axioms nativeMap
#print axioms map_source
#print axioms nativeFallback
#print axioms fallback_source
#print axioms nativeCircle
#print axioms source_reference
end R1Z.PV_AL_CircleNative
