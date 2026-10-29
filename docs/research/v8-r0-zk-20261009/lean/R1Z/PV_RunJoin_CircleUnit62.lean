import R1Z.PV_RunJoin_CircleInstalledTotal55
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CircleUnit62
open Aeneas Aeneas.Std
attribute [local irreducible] R0P.SemSource.circleSample0 R0P.SemSource.circleSample1
  AspisV8R19.SqueezeOracleBridge.decodeState

theorem first (block : Array U8 32#usize) :
    ((R0P.SemSource.circleSample0 (AspisV8R19.SqueezeOracleBridge.decodeState block)).val).1^2+
    ((R0P.SemSource.circleSample0 (AspisV8R19.SqueezeOracleBridge.decodeState block)).val).2^2=1 := by
  have h := (R0P.SemSource.circleSample0 (AspisV8R19.SqueezeOracleBridge.decodeState block)).property
  simpa only [AspisCircleGroupOrder.OnCircle] using h

theorem second (block : Array U8 32#usize) :
    ((R0P.SemSource.circleSample1 (AspisV8R19.SqueezeOracleBridge.decodeState block)).val).1^2+
    ((R0P.SemSource.circleSample1 (AspisV8R19.SqueezeOracleBridge.decodeState block)).val).2^2=1 := by
  have h := (R0P.SemSource.circleSample1 (AspisV8R19.SqueezeOracleBridge.decodeState block)).property
  simpa only [AspisCircleGroupOrder.OnCircle] using h

#print axioms first
#print axioms second
end R1Z.PV_RunJoin_CircleUnit62
