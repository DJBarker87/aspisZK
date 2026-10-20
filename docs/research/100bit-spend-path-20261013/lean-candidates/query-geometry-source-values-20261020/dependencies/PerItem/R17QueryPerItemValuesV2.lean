import R17FibrePointLineNodeActual
import R17CurrentM31Semantics
import R17CurrentCM31Semantics

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace R17QueryPerItemValuesV2

open AspisR1QueryGeometryActual AspisCircleGroupOrder
open R17FibrePointLineNodeActual

def actualCMOps : CM31Ops := R17CurrentCM31Semantics.operations
def actualM31Ops : M31Ops := R17CurrentM31Semantics.operations

/-- The non-looping five-value part of QueryGeometry::for_range after its
three FibreIndex values are available. This preserves the per-query call order:
circle point, parent line x, parent line y, then line z. -/
def perQueryCore (cmops : CM31Ops)
    (ops : M31Ops) (u ix iy : domain.FibreIndex) :
    Result (domain.Point field.M31 × field.M31 × field.M31 × field.M31) := do
  let point ← fast_domain.fibre_point cmops u
  let lineX ← line_node cmops ops ix
  let lineY ← line_node cmops ops iy
  let xx ← ops.mul lineX lineX
  let twice ← ops.double xx
  let lineZ ← ops.sub twice (1#u32)
  pure (point, lineX, lineY, lineZ)

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

/-- A successful per-query value construction has the stored initial circle
coordinates and the two stored first-line values; line z is the same
`2*x^2-1` value formed by the source after those two line calls. Only the
retained CM31 and scalar M31 operation laws are assumptions. -/
theorem successful_perQueryCore_stored
    (u ix iy : domain.FibreIndex)
    (hu : u.val < 262144) (hix : ix.val < 262144) (hiy : iy.val < 262144)
    (point : domain.Point field.M31) (lineX lineY lineZ : field.M31)
    (h : perQueryCore actualCMOps actualM31Ops u ix iy = .ok (point, lineX, lineY, lineZ)) :
    (⟨(R17FibrePointDecodedProduct.decodePoint point).1,
       (R17FibrePointDecodedProduct.decodePoint point).2⟩ : R17TableBasePowerBridge.ZC) =
        R17TableCirclePowerBridge.circleCoords
          (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20
            (⟨u.val, hu⟩ : Fin 262144)) ∧
      decoded lineX = AspisV7ExactOneFoldDomains.storedFirstLineX18
          (⟨ix.val, hix⟩ : Fin 262144) ∧
      decoded lineY = AspisV7ExactOneFoldDomains.storedFirstLineX18
          (⟨iy.val, hiy⟩ : Fin 262144) ∧
      decoded lineZ = 2 * (AspisV7ExactOneFoldDomains.storedFirstLineX18
          (⟨ix.val, hix⟩ : Fin 262144)) ^ 2 - 1 := by
  have hrun := h
  unfold perQueryCore at hrun
  rcases bind_ok_inv hrun with ⟨point0, hpoint, hrun1⟩
  rcases bind_ok_inv hrun1 with ⟨lineX0, hlineX, hrun2⟩
  rcases bind_ok_inv hrun2 with ⟨lineY0, hlineY, hrun3⟩
  rcases bind_ok_inv hrun3 with ⟨xx, hmul, hrun4⟩
  rcases bind_ok_inv hrun4 with ⟨twice, hdouble, hrun5⟩
  rcases bind_ok_inv hrun5 with ⟨lineZ0, hsub, hfinish⟩
  have htuple : (point0, lineX0, lineY0, lineZ0) = (point, lineX, lineY, lineZ) :=
    Result.ok.inj (by simpa only [Pure.pure] using hfinish)
  have hp : point0 = point := by exact congrArg Prod.fst htuple
  have hx : lineX0 = lineX := by
    have h' := congrArg (fun t : domain.Point field.M31 × field.M31 × field.M31 × field.M31 => t.2.1) htuple
    exact h'
  have hy : lineY0 = lineY := by
    have h' := congrArg (fun t : domain.Point field.M31 × field.M31 × field.M31 × field.M31 => t.2.2.1) htuple
    exact h'
  subst point0
  subst lineX0
  subst lineY0
  have hpointStored := R17FibrePointActualSuccess.successful_call_eq_stored
    actualCMOps R17CurrentCM31Semantics.operations_semantics u hu point hpoint
  let ops := actualM31Ops
  have hm : M31OpsSemantics ops := R17CurrentM31Semantics.operations_semantics
  have hxStored := successful_line_node_stored actualCMOps
    R17CurrentCM31Semantics.operations_semantics ops hm ix hix lineX hlineX
  have hyStored := successful_line_node_stored actualCMOps
    R17CurrentCM31Semantics.operations_semantics ops hm iy hiy lineY hlineY
  have hlineZ0 : lineZ0 = lineZ := by
    exact congrArg (fun t : domain.Point field.M31 × field.M31 × field.M31 × field.M31 => t.2.2.2) htuple
  have hzFormula : decoded lineZ = 2 * decoded lineX ^ 2 - 1 := by
    rw [← hlineZ0]
    rw [hm.sub_spec twice (1#u32) lineZ0 hsub, decoded_source_one,
      hm.double_spec xx twice hdouble,
      hm.mul_spec lineX lineX xx hmul]
    ring
  exact ⟨hpointStored, hxStored, hyStored, by rw [hzFormula, hxStored]⟩

#print axioms successful_perQueryCore_stored

/-- In-place source cut for the successful per-query portion of the actual
`query_values_entry` body. It preserves call order and the exact five-element
array construction. The closure-specific `Slice.iter.any` body is an explicit
function argument so this theorem does not import an unproved external axiom. -/
def queryValuesWithAny {E : Type}
    (qerror : E) (u ix iy : domain.FibreIndex)
    (anyCheck : core.slice.iter.Iter field.M31 →
      Result (Bool × core.slice.iter.Iter field.M31)) :
    Result (core.result.Result ((Array field.M31 5#usize) × field.M31) E) := do
  let point ← fast_domain.fibre_point actualCMOps u
  let line_x ← line_node actualCMOps actualM31Ops ix
  let line_y ← line_node actualCMOps actualM31Ops iy
  let m ← actualM31Ops.mul line_x line_x
  let m1 ← actualM31Ops.double m
  let line_z ← actualM31Ops.sub m1 (1#u32)
  let s ← lift (Array.to_slice
    (Array.make 5#usize [point.x, point.y, line_x, line_y, line_z]))
  let i4 ← core.slice.Slice.iter s
  let (b, _) ← anyCheck i4
  if b then ok (core.result.Result.Err qerror)
  else ok (core.result.Result.Ok
    (Array.make 5#usize [point.x, point.y, line_x, line_y, line_z], line_z))

/-- Success in the source cut implies the exact five-slot order, returned
line-z slot, and a successful false result from the explicit iterator-any
boundary. -/
theorem successful_queryValuesWithAny {E : Type}
    (qerror : E) (u ix iy : domain.FibreIndex)
    (anyCheck : core.slice.iter.Iter field.M31 →
      Result (Bool × core.slice.iter.Iter field.M31))
    (arr : Array field.M31 5#usize) (line_z : field.M31)
    (h : queryValuesWithAny qerror u ix iy anyCheck =
      .ok (.Ok (arr, line_z))) :
    ∃ point line_x line_y,
      perQueryCore actualCMOps actualM31Ops u ix iy =
        .ok (point, line_x, line_y, line_z) ∧
      arr = Array.make 5#usize [point.x, point.y, line_x, line_y, line_z] ∧
      ∃ iter iter', anyCheck iter = .ok (false, iter') := by
  unfold queryValuesWithAny at h
  rcases bind_ok_inv h with ⟨point, hpoint, hrest1⟩
  rcases bind_ok_inv hrest1 with ⟨line_x, hline_x, hrest2⟩
  rcases bind_ok_inv hrest2 with ⟨line_y, hline_y, hrest3⟩
  rcases bind_ok_inv hrest3 with ⟨m, hm, hrest4⟩
  rcases bind_ok_inv hrest4 with ⟨m1, hm1, hrest5⟩
  rcases bind_ok_inv hrest5 with ⟨line_z0, hline_z, hrest6⟩
  rcases bind_ok_inv hrest6 with ⟨s, hs, hrest7⟩
  rcases bind_ok_inv hrest7 with ⟨iter, hiter, hrest8⟩
  rcases bind_ok_inv hrest8 with ⟨result, hany, hfinal⟩
  rcases result with ⟨b, iter'⟩
  have hb : b = false := by
    cases b <;> simp_all
  subst b
  have hzero : anyCheck iter = .ok (false, iter') := hany
  change Result.ok (core.result.Result.Ok
    (Array.make 5#usize [point.x, point.y, line_x, line_y, line_z0], line_z0)) =
      Result.ok (core.result.Result.Ok (arr, line_z)) at hfinal
  have hinner : core.result.Result.Ok
      (Array.make 5#usize [point.x, point.y, line_x, line_y, line_z0], line_z0) =
      core.result.Result.Ok (arr, line_z) := Result.ok.inj hfinal
  have htuple : (Array.make 5#usize [point.x, point.y, line_x, line_y, line_z0], line_z0) =
      (arr, line_z) := by
    injection hinner with htuple
  have harr : Array.make 5#usize [point.x, point.y, line_x, line_y, line_z0] = arr :=
    congrArg Prod.fst htuple
  have hline : line_z0 = line_z := congrArg Prod.snd htuple
  subst line_z0
  refine ⟨point, line_x, line_y, ?_, harr.symm, iter, iter', hzero⟩
  simp [perQueryCore, hpoint, hline_x, hline_y, hm, hm1, hline_z]
  rfl

#print axioms successful_queryValuesWithAny

end R17QueryPerItemValuesV2
