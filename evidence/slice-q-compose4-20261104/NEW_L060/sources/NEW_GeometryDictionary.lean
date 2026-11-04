import NEW_GeometryChildren
set_option autoImplicit false
noncomputable section
namespace NEW_GeometryDictionary
open Aeneas Aeneas.Std Result AspisR1
open NEW_GeometryRawInterface
abbrev CE := NEW_GeometryActual.aspis_core.r0.Error
abbrev err : CE := .IndexOutOfRange

def adopted : Port3_NativeGeometryBody.Ops CE :=
  Port5Q1_GeometryTerminal.install (NEB_ActualGeometryModel.install ops err)

def contextual : Port3_NativeGeometryBody.Ops CE :=
  {adopted with op8:=ops.op8,op10:=ops.op10}

/-- All children except the domain-dependent double/sub slots have universal
full Result correspondences; those two are replaced only in their real context. -/
theorem dictionary : ops = contextual := by
  unfold contextual adopted
  rw [NEB_ActualGeometryModel.same_dictionary]
  unfold NEB_GeometryModel.install NEB_GeometryIndices.install
    NEB_GeometryPrimitives.install Port5Q1_GeometryTerminal.install
    Port4C_CollectStd.install Port4C_GeometryGroups.install
    Port4C_GeometryInverse.install Port4C_GeometryStd.install
  unfold ops
  congr 1
  all_goals try rfl
  all_goals try exact funext NEW_GeometryArithmetic.multiply_probe
  all_goals try exact funext NEW_GeometryArithmetic.inverse
  all_goals try exact funext NEW_GeometryChildren.index
  all_goals try exact funext NEW_GeometryPrefix.complete
  all_goals try exact funext NEW_GeometryChildren.line
  all_goals try exact funext NEW_GeometryChildren.point

#print axioms adopted
#print axioms contextual
#print axioms dictionary
end NEW_GeometryDictionary
end
