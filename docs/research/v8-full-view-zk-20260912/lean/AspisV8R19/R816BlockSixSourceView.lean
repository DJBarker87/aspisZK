import AspisV8R19.R807SourceBlock01Binding
import Mathlib.Tactic.FinCases
set_option autoImplicit false
namespace AspisV8R19.R816BlockSixSourceView
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R807SourceBlock01Binding

def block06Rows : Fin 39 → Fin 222 :=
  ![0,1,2,3,4,5,6,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,216,214]
def block06Columns : Fin 39 → Fin 222 :=
  ![0,1,2,3,4,5,6,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,220,221]

theorem block06_rows_exact : (fun i : Fin 39 => rowOrder (flatIndex 6 i)) = block06Rows := by
  funext i
  fin_cases i <;> rfl

theorem block06_columns_exact : (fun i : Fin 39 => colOrder (flatIndex 6 i)) = block06Columns := by
  funext i
  fin_cases i <;> rfl

theorem block06_matrix_generic {R : Type*} (A : Matrix (Fin 222) (Fin 222) R) :
    (A.submatrix rowOrder colOrder).submatrix (flatIndex 6) (flatIndex 6) =
      A.submatrix block06Rows block06Columns := by
  ext i j
  simp only [Matrix.submatrix_apply]
  rw [congrFun block06_rows_exact i, congrFun block06_columns_exact j]

noncomputable def block06SourceMatrix : Matrix (Fin 39) (Fin 39) R807SourceBlock01Binding.M :=
  fixedSourceMatrix.submatrix block06Rows block06Columns

theorem diagonalSourceBlock06_eq_sourceView : diagonalSourceBlock 6 = block06SourceMatrix := by
  exact block06_matrix_generic fixedSourceMatrix

#print axioms block06_rows_exact
#print axioms block06_columns_exact
#print axioms block06_matrix_generic
#print axioms diagonalSourceBlock06_eq_sourceView
end AspisV8R19.R816BlockSixSourceView
