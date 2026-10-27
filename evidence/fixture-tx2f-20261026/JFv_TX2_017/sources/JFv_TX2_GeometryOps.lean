import SAQ_Constructor
import Port5Q1_GeometryTerminal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_GeometryOps
open Aeneas Aeneas.Std Result

def install {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :=
  Port5Q1_GeometryTerminal.install (SAQ_Constructor.install err seed)

theorem fields {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    (install err seed).op15=SAQ_Geometry.point ∧
    (install err seed).op14=SAQ_Geometry.line ∧
    (install err seed).op12=SAQ_Constructor.fibre err ∧
    (install err seed).op9=AspisR1Qm31ArithmeticProbe.field.M31.mul ∧
    (install err seed).op11=Port4C_InverseExecution.inverse_owned := by
  exact ⟨rfl,rfl,rfl,rfl,SAQ_Inverse.source_eq_reference⟩
#print axioms fields
end AspisR1.JFv_TX2_GeometryOps
end
