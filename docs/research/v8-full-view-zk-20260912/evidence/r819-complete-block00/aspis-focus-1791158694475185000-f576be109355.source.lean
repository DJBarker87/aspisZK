import AspisV8R19.R817BlockZeroRow00Binding
import AspisV8R19.R812SourceBlock00Cells03
import AspisV8R19.R752SCC00Matrix

set_option autoImplicit false
namespace AspisV8R19.R818BlockZeroRow03Binding
open AspisV8R19.R815BlockZeroSourceView
open AspisV8R19.R817BlockZeroRow00Binding
open AspisV8R19.R812SourceBlock00Cells03
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R814BlockZeroReindex
open R752SCC00Matrix
noncomputable section
abbrev M := R807SourceBlock01Binding.M

def row03Values : Fin 6 → M := ![1073740136, 1342162795, 536774443, 9450, 208275, 1337250]

theorem source_row03_values :
    (fun j : Fin 6 => fixedSourceMatrix (219 : Fin 222) (block00Columns j)) = row03Values := by
  funext j
  fin_cases j
  · simpa [row03Values, block00Columns] using source_cell_3_0
  · simpa [row03Values, block00Columns] using source_cell_3_1
  · simpa [row03Values, block00Columns] using source_cell_3_2
  · simpa [row03Values, block00Columns] using source_cell_3_3
  · simpa [row03Values, block00Columns] using source_cell_3_4
  · simpa [row03Values, block00Columns] using source_cell_3_5

theorem certificate_row03_values :
    (fun j : Fin 6 => A_scc (3 : Fin 6) j) = row03Values := by
  funext j
  fin_cases j <;> rfl

theorem block00_row_generic_any {R : Type*} (A : Matrix (Fin 222) (Fin 222) R) (i : Fin 6) :
    (A.submatrix block00Rows block00Columns) i =
      fun j : Fin 6 => A (block00Rows i) (block00Columns j) := by
  rfl

theorem source_block00_row3_eq_certificate :
    block00SourceMatrix (3 : Fin 6) = A_scc (3 : Fin 6) := by
  calc
    block00SourceMatrix (3 : Fin 6) =
        (fun j : Fin 6 => fixedSourceMatrix (block00Rows (3 : Fin 6)) (block00Columns j)) :=
      block00_row_generic_any fixedSourceMatrix (3 : Fin 6)
    _ = (fun j : Fin 6 => fixedSourceMatrix (219 : Fin 222) (block00Columns j)) := by rfl
    _ = row03Values := source_row03_values
    _ = (fun j : Fin 6 => A_scc (3 : Fin 6) j) := certificate_row03_values.symm

#print axioms source_row03_values
#print axioms certificate_row03_values
#print axioms block00_row_generic_any
#print axioms source_block00_row3_eq_certificate
end
end AspisV8R19.R818BlockZeroRow03Binding
