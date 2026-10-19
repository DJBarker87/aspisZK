import RawCircleSampleActualModelV4

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result

namespace AspisR1CircleSampleWrapper
namespace RawCircleSamplePointwiseModelV1

open AspisV8R15.ExactTowerBase
open AspisV8R19.SamplerClosureCircleSourceExecution
open AspisV8R19.SamplerClosureProductCorrectness
open AspisV8R19.SamplerCirclePolicy
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge AspisWideTower
open AspisR0.ChordGeometry
open R0P.SemSource

/-- The coordinates of the actual wrapper point after decoding its stored
    fields and embedding them into the wide model field. -/
def actualWideCoordinates (p : circle.SecureCirclePoint) : WideExact × WideExact :=
  (algebraMap QM31Exact WideExact (decode (toR72QM p.x)),
   algebraMap QM31Exact WideExact (decode (toR72QM p.y)))

def modelPoint (row : r0_transcript.CircleRow) (s : State) : Point WideExact :=
  match row with
  | .First => circleSample0 s
  | .Second => circleSample1 s

private theorem embedCirclePoint_val (z : Point CircleParam) :
    (R0P.SemSource.embedCirclePoint z).val =
      (algebraMap CircleParam WideExact z.1.1,
       algebraMap CircleParam WideExact z.1.2) := rfl

private theorem actualWideCoordinates_fromR72
    (p : AspisR72Sampler.circle.SecureCirclePoint) :
    actualWideCoordinates (fromR72Point p) =
      (algebraMap QM31Exact WideExact (decode p.x),
       algebraMap QM31Exact WideExact (decode p.y)) := by
  cases p with
  | mk x y =>
    cases x with
    | mk c0 c1 =>
      cases c0 with
      | mk a b =>
        cases c1 with
        | mk c d =>
          cases y with
          | mk e f =>
            cases e with
            | mk g h =>
              cases f with
              | mk i j => rfl

theorem actual_sample_coordinates_eq_model
    (block : Array Std.U8 32#usize) (row : r0_transcript.CircleRow)
    (q : field.QM31) (p : circle.SecureCirclePoint)
    (hsample : sampler.qm31_sample block = .ok q)
    (hq : Canonical (toR72QM q))
    (hout : sampler.circle_sample block row = .ok p) :
    actualWideCoordinates p = (modelPoint row (decodeState block)).val := by
  have hparameter := RawCircleSampleActualModelV4.actual_sample_parameter_eq_model
    block q hsample
  cases hr : circle.secure_ood_circle_point_from_parameter q with
  | fail e =>
      simp [sampler.circle_sample, hsample, hr] at hout
  | div =>
      simp [sampler.circle_sample, hsample, hr] at hout
  | ok result =>
      cases result with
      | Ok securePoint =>
          have hrun := RawCircleSampleEmittedWrapperLaw.success_returns_point
            block row q securePoint hsample hr
          have hp : securePoint = p := Result.ok.inj (hrun.symm.trans hout)
          subst p
          obtain ⟨p72, hr72, hfrom, him, _, _, hmapped, _⟩ :=
            RawCircleSampleActualSecureBridgeV1.wrapper_secure_success_circle_facts
              q hq securePoint hr
          have hcoords := actualWideCoordinates_fromR72 p72
          have hbase : decodePoint p72 = AspisV8R19.SamplerCirclePolicy.point
              (decode (toR72QM q)) := hmapped
          have hwide : actualWideCoordinates securePoint =
              (algebraMap QM31Exact WideExact (AspisV8R19.SamplerCirclePolicy.point
                  (decode (toR72QM q))).1,
               algebraMap QM31Exact WideExact (AspisV8R19.SamplerCirclePolicy.point
                  (decode (toR72QM q))).2) := by
            rw [← hfrom]
            rw [hcoords]
            exact congrArg (fun xy : QM31Exact × QM31Exact =>
              (algebraMap QM31Exact WideExact xy.1,
               algebraMap QM31Exact WideExact xy.2)) hbase
          have hwideModel : actualWideCoordinates securePoint =
              (algebraMap QM31Exact WideExact
                (AspisV8R19.SamplerCirclePolicy.point
                  (qm31Sample (decodeState block))).1,
               algebraMap QM31Exact WideExact
                (AspisV8R19.SamplerCirclePolicy.point
                  (qm31Sample (decodeState block))).2) := by
            rw [← hparameter]
            exact hwide
          cases row with
          | First =>
              change actualWideCoordinates securePoint =
                (circleSample0 (decodeState block)).val
              rw [R0P.SemSource.circleSample0, R0P.SemSource.circleSampleParameter0,
                R0P.SemSource.circleSampleParameterWith_accepted circleFallback0
                  (qm31Sample (decodeState block))]
              · rw [embedCirclePoint_val]
                exact hwideModel
              · rw [← hparameter]
                exact him
          | Second =>
              change actualWideCoordinates securePoint =
                (circleSample1 (decodeState block)).val
              rw [R0P.SemSource.circleSample1, R0P.SemSource.circleSampleParameter1,
                R0P.SemSource.circleSampleParameterWith_accepted circleFallback1
                  (qm31Sample (decodeState block))]
              · rw [embedCirclePoint_val]
                exact hwideModel
              · rw [← hparameter]
                exact him
      | Err err =>
          have him : (decode (toR72QM q)).im = 0 := by
            by_contra hnonzero
            have hr72 :
                AspisR72Sampler.circle.secure_ood_circle_point_from_parameter
                  (toR72QM q) = .ok (.Ok (encodePoint
                    (AspisV8R19.SamplerCirclePolicy.point (decode (toR72QM q))))) := by
              rw [AspisV8R19.SamplerClosureCircleSourceExecution.source_execution
                (toR72QM q) hq]
              rw [AspisV8R19.SamplerCirclePolicy.outside_map
                (decode (toR72QM q)) hnonzero]
              rfl
            have hwrapper : circle.secure_ood_circle_point_from_parameter q =
                .ok (.Ok (fromR72Point (encodePoint
                  (AspisV8R19.SamplerCirclePolicy.point (decode (toR72QM q)))))) := by
              rw [RawCircleSampleEmittedWrapperLaw.secure_circle_eq_r72, hr72]
              rfl
            have hfalse := hwrapper.symm.trans hr
            cases hfalse
          have hmodelzero : (qm31Sample (decodeState block)).im = 0 := by
            rw [← hparameter]
            exact him
          cases row with
          | First =>
              have hrun := RawCircleSampleActualFallbackResultV4.firstFallbackActual
                block q err hsample hr
              have hp : p = RawCircleSampleActualFallbackCircleV2.fallbackPoint0 :=
                (Result.ok.inj (hrun.symm.trans hout)).symm
              subst p
              have hcoords := RawCircleSampleActualFallbackCoordinatesV1.firstFallbackCoordinates
              change actualWideCoordinates
                  RawCircleSampleActualFallbackCircleV2.fallbackPoint0 =
                (circleSample0 (decodeState block)).val
              rw [R0P.SemSource.circleSample0, R0P.SemSource.circleSampleParameter0,
                circleSampleParameterWith_rejected circleFallback0
                  (qm31Sample (decodeState block)) hmodelzero]
              exact hcoords
          | Second =>
              have hrun := RawCircleSampleActualFallbackResultV4.secondFallbackActual
                block q err hsample hr
              have hp : p = RawCircleSampleActualFallbackCircleV2.fallbackPoint1 :=
                (Result.ok.inj (hrun.symm.trans hout)).symm
              subst p
              have hcoords := RawCircleSampleActualFallbackCoordinatesV1.secondFallbackCoordinates
              change actualWideCoordinates
                  RawCircleSampleActualFallbackCircleV2.fallbackPoint1 =
                (circleSample1 (decodeState block)).val
              rw [R0P.SemSource.circleSample1, R0P.SemSource.circleSampleParameter1,
                circleSampleParameterWith_rejected circleFallback1
                  (qm31Sample (decodeState block)) hmodelzero]
              exact hcoords
#print axioms actual_sample_coordinates_eq_model

end RawCircleSamplePointwiseModelV1
end AspisR1CircleSampleWrapper
