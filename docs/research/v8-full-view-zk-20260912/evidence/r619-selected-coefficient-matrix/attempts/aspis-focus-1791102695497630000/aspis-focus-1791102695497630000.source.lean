import AspisR618SelectedMatrix.Funs
import AspisV8R19.R159WideBaseExecution
import AspisV8R19.R161WrappedMulExecution

set_option autoImplicit false

namespace AspisV8R19.R619MatrixArithmeticBridge
open Aeneas Aeneas.Std
open AspisV8R15.ExactTowerBase (M31Exact)
open AspisV8R19.ComplexBaseExecution (encodeBase)

theorem actual_add_eq_reference_all (x y : Aeneas.Std.U32) :
    AspisR618SelectedMatrix.aspis_core.field.M31.add x y =
      AspisR156FullFreeze.aspis_core.field.M31.add x y := by
  simp only [AspisR618SelectedMatrix.aspis_core.field.M31.add,
    AspisR156FullFreeze.aspis_core.field.M31.add,
    AspisR618SelectedMatrix.aspis_core.field.r91_raw_add,
    AspisR156FullFreeze.aspis_core.field.r91_raw_add,
    AspisR156FullFreeze.aspis_core.field.P]

theorem actual_sub_eq_reference_all (x y : Aeneas.Std.U32) :
    AspisR618SelectedMatrix.aspis_core.field.M31.sub x y =
      AspisR156FullFreeze.aspis_core.field.M31.sub x y := by
  simp only [AspisR618SelectedMatrix.aspis_core.field.M31.sub,
    AspisR156FullFreeze.aspis_core.field.M31.sub,
    AspisR618SelectedMatrix.aspis_core.field.r91_raw_sub,
    AspisR156FullFreeze.aspis_core.field.r91_raw_sub,
    AspisR156FullFreeze.aspis_core.field.P]

theorem actual_neg_eq_reference_all (x : Aeneas.Std.U32) :
    AspisR618SelectedMatrix.aspis_core.field.M31.neg x =
      AspisR156FullFreeze.aspis_core.field.M31.neg x := by
  simp only [AspisR618SelectedMatrix.aspis_core.field.M31.neg,
    AspisR156FullFreeze.aspis_core.field.M31.neg]

theorem actual_double_eq_reference_all (x : Aeneas.Std.U32) :
    AspisR618SelectedMatrix.aspis_core.field.M31.double x =
      AspisR156FullFreeze.aspis_core.field.M31.double x := by
  simp only [AspisR618SelectedMatrix.aspis_core.field.M31.double,
    AspisR156FullFreeze.aspis_core.field.M31.double,
    actual_add_eq_reference_all]

theorem actual_add_eq_reference (a b : M31Exact) :
    AspisR618SelectedMatrix.aspis_core.field.M31.add (encodeBase a) (encodeBase b) =
      AspisR156FullFreeze.aspis_core.field.M31.add (encodeBase a) (encodeBase b) :=
  actual_add_eq_reference_all _ _

end AspisV8R19.R619MatrixArithmeticBridge
