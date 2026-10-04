import AspisV8R19.R619MatrixArithmeticBridge
import AspisV8R19.ProductCorrectness
set_option autoImplicit false
namespace AspisV8R19.R620MatrixAction
open Aeneas Aeneas.Std
open AspisV8R19.ComplexBaseExecution (encodeBase)
open AspisV8R15.ExactTowerBase (M31Exact QM31Exact)

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


def arrayAt {α : Type} {n : Usize} (xs : Aeneas.Std.Array α n)
    (i : Fin n.val) : α := xs.val[i.val]'(by rw [xs.property]; exact i.isLt)

def selectedMatrix (a b c d : M31Exact) :
    Aeneas.Std.Array (Aeneas.Std.Array U32 4#usize) 4#usize :=
  Aeneas.Std.Array.make 4#usize [
    Aeneas.Std.Array.make 4#usize [encodeBase a, encodeBase b, encodeBase c, encodeBase d],
    Aeneas.Std.Array.make 4#usize [encodeBase (-b), encodeBase a, encodeBase (-d), encodeBase c],
    Aeneas.Std.Array.make 4#usize [encodeBase (2*c-d), encodeBase (c+2*d), encodeBase a, encodeBase b],
    Aeneas.Std.Array.make 4#usize [encodeBase (-(c+2*d)), encodeBase (2*c-d), encodeBase (-b), encodeBase a]
  ]

def matrixCoordinate (m : Aeneas.Std.Array (Aeneas.Std.Array U32 4#usize) 4#usize)
    (e f g h : M31Exact) (k : Fin 4) : M31Exact :=
  e * ((arrayAt (arrayAt m ⟨0, by decide⟩) k).val : M31Exact) +
  f * ((arrayAt (arrayAt m ⟨1, by decide⟩) k).val : M31Exact) +
  g * ((arrayAt (arrayAt m ⟨2, by decide⟩) k).val : M31Exact) +
  h * ((arrayAt (arrayAt m ⟨3, by decide⟩) k).val : M31Exact)

def matrixAction (m : Aeneas.Std.Array (Aeneas.Std.Array U32 4#usize) 4#usize)
    (e f g h : M31Exact) : QM31Exact :=
  ⟨⟨matrixCoordinate m e f g h ⟨0, by decide⟩,
      matrixCoordinate m e f g h ⟨1, by decide⟩⟩,
    ⟨matrixCoordinate m e f g h ⟨2, by decide⟩,
      matrixCoordinate m e f g h ⟨3, by decide⟩⟩⟩

theorem actual_matrix_action (a b c d e f g h : M31Exact) :
    ∃ m : Aeneas.Std.Array (Aeneas.Std.Array U32 4#usize) 4#usize,
      AspisR618SelectedMatrix.query_arithmetic.r83_matrix
        (AspisV8R19.R619MatrixArithmeticBridge.matrixInput a b c d) = .ok m ∧
      matrixAction m e f g h =
        (⟨⟨a,b⟩,⟨c,d⟩⟩ : QM31Exact) * ⟨⟨e,f⟩,⟨g,h⟩⟩ := by
  refine ⟨selectedMatrix a b c d, ?_, ?_⟩
  · simpa [selectedMatrix, AspisV8R19.R619MatrixArithmeticBridge.matrixInput] using
      AspisV8R19.R619MatrixArithmeticBridge.actual_matrix_execution a b c d
  · have hcoordinates : matrixAction (selectedMatrix a b c d) e f g h =
        (⟨⟨a*e-b*f+(2*c-d)*g-(c+2*d)*h,
           b*e+a*f+(c+2*d)*g+(2*c-d)*h⟩,
         ⟨c*e-d*f+a*g-b*h,
           d*e+c*f+b*g+a*h⟩⟩ : QM31Exact) := by
      apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
        simp [matrixAction, matrixCoordinate, arrayAt, selectedMatrix,
          Aeneas.Std.Array.make, AspisV8R19.ComplexBaseExecution.encodeBase_val,
          ZMod.natCast_zmod_val] <;> ring
    exact hcoordinates.trans (qm31_product_coordinates a b c d e f g h).symm

#print axioms qm31_product_coordinates
#print axioms actual_matrix_action
end AspisV8R19.R620MatrixAction
