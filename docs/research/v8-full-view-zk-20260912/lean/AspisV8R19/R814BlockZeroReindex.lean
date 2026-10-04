import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R803LiteralSupplementaryEntries

set_option autoImplicit false
namespace AspisV8R19.R814BlockZeroReindex
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R803LiteralSupplementaryEntries

def block00Columns : Fin 6 → Fin 222 := ![214,215,216,217,218,219]

theorem block00_columns_exact : (fun j : Fin 6 => colOrder (flatIndex 0 j)) = block00Columns := by
  funext j
  fin_cases j <;> rfl

theorem block00_row_generic {R : Type*} (A : Matrix (Fin 222) (Fin 222) R) (i : Fin 6) :
    ((A.submatrix rowOrder colOrder).submatrix (flatIndex 0) (flatIndex 0)) i =
      fun j => A (rowOrder (flatIndex 0 i)) (block00Columns j) := by
  funext j
  simp only [Matrix.submatrix_apply]
  rw [← congrFun block00_columns_exact j]

#print axioms block00_columns_exact
#print axioms block00_row_generic
end AspisV8R19.R814BlockZeroReindex
