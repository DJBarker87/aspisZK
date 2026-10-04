import AspisV8R19.R814BlockZeroReindex
set_option autoImplicit false
namespace AspisV8R19.R815BlockZeroSourceView
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R814BlockZeroReindex
open AspisV8R19.R807SourceBlock01Binding

def block00Rows : Fin 6 → Fin 222 := ![215,217,218,219,220,221]
theorem block00_rows_exact : (fun i : Fin 6 => rowOrder (flatIndex 0 i)) = block00Rows := by
  funext i
  fin_cases i <;> rfl

theorem block00_matrix_generic {R : Type*} (A : Matrix (Fin 222) (Fin 222) R) :
    (A.submatrix rowOrder colOrder).submatrix (flatIndex 0) (flatIndex 0) =
      A.submatrix block00Rows block00Columns := by
  ext i j
  simp only [Matrix.submatrix_apply]
  rw [congrFun block00_rows_exact i, congrFun block00_columns_exact j]

noncomputable def block00SourceMatrix : Matrix (Fin 6) (Fin 6) R807SourceBlock01Binding.M :=
  fixedSourceMatrix.submatrix block00Rows block00Columns

theorem diagonalSourceBlock00_eq_sourceView : diagonalSourceBlock 0 = block00SourceMatrix := by
  exact block00_matrix_generic fixedSourceMatrix

#print axioms block00_rows_exact
#print axioms block00_matrix_generic
#print axioms diagonalSourceBlock00_eq_sourceView
end AspisV8R19.R815BlockZeroSourceView
