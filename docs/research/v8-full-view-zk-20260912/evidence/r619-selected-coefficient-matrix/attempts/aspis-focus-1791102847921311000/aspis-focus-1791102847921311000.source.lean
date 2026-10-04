import AspisR618SelectedMatrix.Funs
import AspisV8R19.R159WideBaseExecution
import AspisV8R19.R161WrappedMulExecution
import AspisV8R19.ProductCorrectness

set_option autoImplicit false

namespace AspisV8R19.R619MatrixArithmeticBridge
open Aeneas Aeneas.Std
open AspisV8R15.ExactTowerBase (M31Exact QM31Exact)
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
    AspisR156FullFreeze.aspis_core.field.M31.neg,
    AspisR156FullFreeze.aspis_core.field.P]

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


open AspisV8R15.ExactTowerBase (M31Exact QM31Exact)

 theorem actual_add_encode (a b : M31Exact) :
    AspisR618SelectedMatrix.aspis_core.field.M31.add (encodeBase a) (encodeBase b) =
      .ok (encodeBase (a + b)) := by
  rw [actual_add_eq_reference_all]
  exact AspisV8R19.R159WideBaseExecution.add_encode a b

theorem actual_sub_encode (a b : M31Exact) :
    AspisR618SelectedMatrix.aspis_core.field.M31.sub (encodeBase a) (encodeBase b) =
      .ok (encodeBase (a - b)) := by
  rw [actual_sub_eq_reference_all]
  exact AspisV8R19.R159WideBaseExecution.sub_encode a b

theorem actual_double_encode (a : M31Exact) :
    AspisR618SelectedMatrix.aspis_core.field.M31.double (encodeBase a) =
      .ok (encodeBase (a + a)) := by
  rw [actual_double_eq_reference_all]
  exact AspisV8R19.R159WideBaseExecution.double_encode a

theorem actual_neg_encode (a : M31Exact) :
    AspisR618SelectedMatrix.aspis_core.field.M31.neg (encodeBase a) =
      .ok (encodeBase (-a)) := by
  rw [actual_neg_eq_reference_all]
  exact AspisV8R19.R161WrappedMulExecution.neg_encode a

def matrixInput (a b c d : M31Exact) : AspisR618SelectedMatrix.aspis_core.field.QM31 :=
  ⟨⟨encodeBase a, encodeBase b⟩, ⟨encodeBase c, encodeBase d⟩⟩

theorem actual_matrix_execution (a b c d : M31Exact) :
    AspisR618SelectedMatrix.query_arithmetic.r83_matrix (matrixInput a b c d) =
      .ok (Aeneas.Std.Array.make 4#usize [
        Aeneas.Std.Array.make 4#usize [encodeBase a, encodeBase b, encodeBase c, encodeBase d],
        Aeneas.Std.Array.make 4#usize [encodeBase (-b), encodeBase a, encodeBase (-d), encodeBase c],
        Aeneas.Std.Array.make 4#usize [encodeBase (2*c-d), encodeBase (c+2*d), encodeBase a, encodeBase b],
        Aeneas.Std.Array.make 4#usize [encodeBase (-(c+2*d)), encodeBase (2*c-d), encodeBase (-b), encodeBase a]
      ]) := by
  simp only [AspisR618SelectedMatrix.query_arithmetic.r83_matrix, matrixInput,
    actual_double_encode, actual_sub_encode, actual_add_encode, actual_neg_encode,
    bind_tc_ok]
  have hcd : c + c - d = 2*c-d := by ring
  have hsum : c + (d+d) = c+2*d := by ring
  rw [hcd, hsum]

theorem qm31_product_coordinates (a b c d e f g h : M31Exact) :
    (⟨⟨a,b⟩,⟨c,d⟩⟩ : QM31Exact) * ⟨⟨e,f⟩,⟨g,h⟩⟩ =
      ⟨⟨a*e-b*f+(2*c-d)*g-(c+2*d)*h,
         b*e+a*f+(c+2*d)*g+(2*c-d)*h⟩,
       ⟨c*e-d*f+a*g-b*h,
         d*e+c*f+b*g+a*h⟩⟩ := by
  apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,
      AspisV8R15.ExactTowerBase.qm31R_re,
      AspisV8R15.ExactTowerBase.qm31R_im,
      QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero] <;> ring

#print axioms actual_add_eq_reference_all
#print axioms actual_sub_eq_reference_all
#print axioms actual_neg_eq_reference_all
#print axioms actual_double_eq_reference_all
#print axioms actual_matrix_execution
#print axioms qm31_product_coordinates

end AspisV8R19.R619MatrixArithmeticBridge
