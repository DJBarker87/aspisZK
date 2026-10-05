import AspisV8R19.R817BlockZeroRow00Binding
import AspisV8R19.R812SourceBlock00Cells01
import AspisV8R19.R752SCC00Matrix

set_option autoImplicit false
namespace AspisV8R19.R818BlockZeroRow01Binding
open AspisV8R19.R815BlockZeroSourceView
open AspisV8R19.R817BlockZeroRow00Binding
open AspisV8R19.R812SourceBlock00Cells01
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R814BlockZeroReindex
open R752SCC00Matrix
noncomputable section
abbrev M := R807SourceBlock01Binding.M

def row01Values : Fin 6 → M := ![1879053113, 268469909, 1879289363, 2147362972, 2146642072, 2141592622]

theorem source_row01_values :
    (fun j : Fin 6 => fixedSourceMatrix (217 : Fin 222) (block00Columns j)) = row01Values := by
  funext j
  fin_cases j
  · simpa [row01Values, block00Columns] using source_cell_1_0
  · simpa [row01Values, block00Columns] using source_cell_1_1
  · simpa [row01Values, block00Columns] using source_cell_1_2
  · simpa [row01Values, block00Columns] using source_cell_1_3
  · simpa [row01Values, block00Columns] using source_cell_1_4
  · simpa [row01Values, block00Columns] using source_cell_1_5

theorem certificate_row01_values :
    (fun j : Fin 6 => A_scc (1 : Fin 6) j) = row01Values := by
  funext j
  fin_cases j <;> rfl

theorem source_block00_row1_eq_certificate :
    block00SourceMatrix (1 : Fin 6) = A_scc (1 : Fin 6) := by
  calc
    block00SourceMatrix (1 : Fin 6) =
        (fun j : Fin 6 => fixedSourceMatrix (217 : Fin 222) (block00Columns j)) := by
      apply block00_row0_generic
    _ = row01Values := source_row01_values
    _ = (fun j : Fin 6 => A_scc (1 : Fin 6) j) := certificate_row01_values.symm

#print axioms source_row01_values
#print axioms certificate_row01_values
#print axioms source_block00_row1_eq_certificate
end
end AspisV8R19.R818BlockZeroRow01Binding
