import AspisV8R19.R815BlockZeroSourceView
import AspisV8R19.R812SourceBlock00Cells00
import AspisV8R19.R752SCC00Matrix

set_option autoImplicit false
namespace AspisV8R19.R817BlockZeroRow00Binding
open AspisV8R19.R815BlockZeroSourceView
open AspisV8R19.R812SourceBlock00Cells00
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R803LiteralSupplementaryEntries
open AspisV8R19.R814BlockZeroReindex
open R752SCC00Matrix
noncomputable section
abbrev M := R807SourceBlock01Binding.M

def row00Values : Fin 6 → M := ![45, 45, 1073741711, 2147483527, 672, 27444]

theorem block00_row0_index : block00Rows (0 : Fin 6) = (215 : Fin 222) := by rfl

theorem source_row00_values :
    (fun j : Fin 6 => fixedSourceMatrix (215 : Fin 222) (block00Columns j)) = row00Values := by
  funext j
  fin_cases j
  · simpa [row00Values, block00Columns] using source_cell_0_0
  · simpa [row00Values, block00Columns] using source_cell_0_1
  · simpa [row00Values, block00Columns] using source_cell_0_2
  · simpa [row00Values, block00Columns] using source_cell_0_3
  · simpa [row00Values, block00Columns] using source_cell_0_4
  · simpa [row00Values, block00Columns] using source_cell_0_5

theorem certificate_row00_values :
    (fun j : Fin 6 => A_scc (0 : Fin 6) j) = row00Values := by
  funext j
  fin_cases j <;> rfl

theorem source_block00_row0_eq_certificate :
    block00SourceMatrix (0 : Fin 6) = A_scc (0 : Fin 6) := by
  funext j
  change fixedSourceMatrix (block00Rows (0 : Fin 6)) (block00Columns j) = A_scc (0 : Fin 6) j
  rw [block00_row0_index]
  exact (congrFun source_row00_values j).trans (congrFun certificate_row00_values j).symm

#print axioms block00_row0_index
#print axioms source_row00_values
#print axioms certificate_row00_values
#print axioms source_block00_row0_eq_certificate
end
end AspisV8R19.R817BlockZeroRow00Binding
