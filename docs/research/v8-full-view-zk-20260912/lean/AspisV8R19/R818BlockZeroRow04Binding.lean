import AspisV8R19.R817BlockZeroRow00Binding
import AspisV8R19.R812SourceBlock00Cells04
import AspisV8R19.R752SCC00Matrix

set_option autoImplicit false
namespace AspisV8R19.R818BlockZeroRow04Binding
open AspisV8R19.R815BlockZeroSourceView
open AspisV8R19.R817BlockZeroRow00Binding
open AspisV8R19.R812SourceBlock00Cells04
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R814BlockZeroReindex
open R752SCC00Matrix
noncomputable section
abbrev M := R807SourceBlock01Binding.M

def row04Values : Fin 6 → M := ![0, 536871193, 536871193, 0, 2147479747, 2147465797]

theorem source_row04_values :
    (fun j : Fin 6 => fixedSourceMatrix (220 : Fin 222) (block00Columns j)) = row04Values := by
  funext j
  fin_cases j
  · simpa [row04Values, block00Columns] using source_cell_4_0
  · simpa [row04Values, block00Columns] using source_cell_4_1
  · simpa [row04Values, block00Columns] using source_cell_4_2
  · simpa [row04Values, block00Columns] using source_cell_4_3
  · simpa [row04Values, block00Columns] using source_cell_4_4
  · simpa [row04Values, block00Columns] using source_cell_4_5

theorem certificate_row04_values :
    (fun j : Fin 6 => A_scc (4 : Fin 6) j) = row04Values := by
  funext j
  fin_cases j <;> rfl

theorem block00_row_generic_any {R : Type*} (A : Matrix (Fin 222) (Fin 222) R) (i : Fin 6) :
    (A.submatrix block00Rows block00Columns) i =
      fun j : Fin 6 => A (block00Rows i) (block00Columns j) := by
  rfl

theorem source_block00_row4_eq_certificate :
    block00SourceMatrix (4 : Fin 6) = A_scc (4 : Fin 6) := by
  calc
    block00SourceMatrix (4 : Fin 6) =
        (fun j : Fin 6 => fixedSourceMatrix (block00Rows (4 : Fin 6)) (block00Columns j)) :=
      block00_row_generic_any fixedSourceMatrix (4 : Fin 6)
    _ = (fun j : Fin 6 => fixedSourceMatrix (220 : Fin 222) (block00Columns j)) := by rfl
    _ = row04Values := source_row04_values
    _ = (fun j : Fin 6 => A_scc (4 : Fin 6) j) := certificate_row04_values.symm

#print axioms source_row04_values
#print axioms certificate_row04_values
#print axioms block00_row_generic_any
#print axioms source_block00_row4_eq_certificate
end
end AspisV8R19.R818BlockZeroRow04Binding
