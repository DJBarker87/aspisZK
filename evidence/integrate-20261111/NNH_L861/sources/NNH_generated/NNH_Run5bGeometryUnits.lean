import NNH_Tx2SlotTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bGeometryUnits
open Aeneas Aeneas.Std Result

theorem canonical_one : NFN_NEW_GeometryDictionary.adopted.op7 = (.ok 1#u32 : Result U32) := rfl

theorem installed_one {C : Type} (err : C) (base : Port3_NativeGeometryBody.Ops C) :
 (Port5Q1_GeometryTerminal.install (SAQ_Constructor.install err base)).op7 = (.ok 1#u32 : Result U32) :=
 SAQ_Constructor.one err base

theorem installed_inverse {C : Type} (err : C) (base : Port3_NativeGeometryBody.Ops C) (x : U32) :
 (Port5Q1_GeometryTerminal.install (SAQ_Constructor.install err base)).op11 x =
 Port4C_InverseExecution.inverse_owned x := by
 change SAQ_Inverse.source x = Port4C_InverseExecution.inverse_owned x
 rw [SAQ_Inverse.source_eq_reference]
#print axioms canonical_one
#print axioms installed_one
#print axioms installed_inverse
end AspisR1.NNH_Run5bGeometryUnits
end
