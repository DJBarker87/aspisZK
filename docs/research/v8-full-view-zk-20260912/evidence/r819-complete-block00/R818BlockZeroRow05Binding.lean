import AspisV8R19.R817BlockZeroRow00Binding
import AspisV8R19.R812SourceBlock00Cells05
import AspisV8R19.R752SCC00Matrix

set_option autoImplicit false
namespace AspisV8R19.R818BlockZeroRow05Binding
open AspisV8R19.R815BlockZeroSourceView
open AspisV8R19.R817BlockZeroRow00Binding
open AspisV8R19.R812SourceBlock00Cells05
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R814BlockZeroReindex
open R752SCC00Matrix
noncomputable section
abbrev M := R807SourceBlock01Binding.M

def row05Values : Fin 6 → M := ![0, 0, 536871193, 0, 0, 2147479747]

theorem source_row05_values :
    (fun j : Fin 6 => fixedSourceMatrix (221 : Fin 222) (block00Columns j)) = row05Values := by
  funext j
  fin_cases j
  · simpa [row05Values, block00Columns] using source_cell_5_0
  · simpa [row05Values, block00Columns] using source_cell_5_1
  · simpa [row05Values, block00Columns] using source_cell_5_2
  · simpa [row05Values, block00Columns] using source_cell_5_3
  · simpa [row05Values, block00Columns] using source_cell_5_4
  · simpa [row05Values, block00Columns] using source_cell_5_5

theorem certificate_row05_values :
    (fun j : Fin 6 => A_scc (5 : Fin 6) j) = row05Values := by
  funext j
  fin_cases j <;> rfl

theorem block00_row_generic_any {R : Type*} (A : Matrix (Fin 222) (Fin 222) R) (i : Fin 6) :
    (A.submatrix block00Rows block00Columns) i =
      fun j : Fin 6 => A (block00Rows i) (block00Columns j) := by
  rfl

theorem source_block00_row5_eq_certificate :
    block00SourceMatrix (5 : Fin 6) = A_scc (5 : Fin 6) := by
  calc
    block00SourceMatrix (5 : Fin 6) =
        (fun j : Fin 6 => fixedSourceMatrix (block00Rows (5 : Fin 6)) (block00Columns j)) :=
      block00_row_generic_any fixedSourceMatrix (5 : Fin 6)
    _ = (fun j : Fin 6 => fixedSourceMatrix (221 : Fin 222) (block00Columns j)) := by rfl
    _ = row05Values := source_row05_values
    _ = (fun j : Fin 6 => A_scc (5 : Fin 6) j) := certificate_row05_values.symm

#print axioms source_row05_values
#print axioms certificate_row05_values
#print axioms block00_row_generic_any
#print axioms source_block00_row5_eq_certificate
end
end AspisV8R19.R818BlockZeroRow05Binding
