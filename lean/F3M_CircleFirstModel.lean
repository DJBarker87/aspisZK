import F3M_CircleMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_CircleFirstModel
open Aeneas Aeneas.Std
attribute [local irreducible] R0P.SemSource.circleSample0 R0P.SemSource.circleSample1

theorem first (block : Array U8 32#usize) :
    AspisR1CircleSampleWrapper.R4TransportCircleCoordinates.model block .First=
      R0P.SemSource.circleSample0 (AspisV8R19.SqueezeOracleBridge.decodeState block) := by
  rfl

#print axioms first
end AspisR1.F3M_CircleFirstModel
end
