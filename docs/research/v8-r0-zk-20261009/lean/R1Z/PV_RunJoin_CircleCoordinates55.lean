import R1Z.PV_RunJoin_CircleTotal55
set_option autoImplicit false
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_RunJoin_CircleCoordinates55
open PV_RunJoin_CircleR72Carrier52
open AspisV8R15.ExactTowerBase
open AspisV8R19.SamplerClosureCircleSourceExecution
open AspisV8R19.SamplerClosureProductCorrectness

def coordinates (p : Point) : AspisWideTower.WideExact × AspisWideTower.WideExact :=
  (algebraMap QM31Exact AspisWideTower.WideExact (decode (encQ p.1)),
   algebraMap QM31Exact AspisWideTower.WideExact (decode (encQ p.2)))

theorem encoded (p : QM31Exact × QM31Exact) :
    coordinates (decPoint (encodePoint p))=
      (algebraMap QM31Exact AspisWideTower.WideExact p.1,
       algebraMap QM31Exact AspisWideTower.WideExact p.2) := by
  change (algebraMap QM31Exact AspisWideTower.WideExact (decode ((encPoint (decPoint (encodePoint p))).x)),
    algebraMap QM31Exact AspisWideTower.WideExact (decode ((encPoint (decPoint (encodePoint p))).y)))=_
  rw [point_source]
  exact congrArg (fun q : QM31Exact × QM31Exact =>
    (algebraMap QM31Exact AspisWideTower.WideExact q.1,
     algebraMap QM31Exact AspisWideTower.WideExact q.2)) (decode_point p)

theorem chosen (block : Array U8 32#usize) (row : Bool) :
    coordinates (decPoint (encodePoint (AspisV8R19.SamplerCirclePolicy.point (PV_RunJoin_CircleTotal55.chosen block row))))=
      (if row then R0P.SemSource.circleSample1 (AspisV8R19.SqueezeOracleBridge.decodeState block)
       else R0P.SemSource.circleSample0 (AspisV8R19.SqueezeOracleBridge.decodeState block)).1 := by
  rw [encoded]
  unfold PV_RunJoin_CircleTotal55.chosen
  let t := R0P.SemSource.qm31Sample (AspisV8R19.SqueezeOracleBridge.decodeState block)
  by_cases hi : t.im≠0
  · cases row <;> simp only [if_pos hi,Bool.false_eq_true,if_false,if_true,
      R0P.SemSource.circleSample0,R0P.SemSource.circleSample1,R0P.SemSource.circleSampleParameter0,
      R0P.SemSource.circleSampleParameter1,R0P.SemSource.circleSampleParameterWith_accepted _ _ hi,
      R0P.SemSource.embedCirclePoint]
  · have hz : t.im=0 := not_ne_iff.mp hi
    cases row <;> simp only [if_neg hi,Bool.false_eq_true,if_false,if_true,
      R0P.SemSource.circleSample0,R0P.SemSource.circleSample1,R0P.SemSource.circleSampleParameter0,
      R0P.SemSource.circleSampleParameter1,R0P.SemSource.circleSampleParameterWith_rejected _ _ hz,
      R0P.SemSource.circleFallback0,R0P.SemSource.circleFallback1,R0P.SemSource.embedCirclePoint]

#print axioms coordinates
#print axioms encoded
#print axioms chosen
end R1Z.PV_RunJoin_CircleCoordinates55
