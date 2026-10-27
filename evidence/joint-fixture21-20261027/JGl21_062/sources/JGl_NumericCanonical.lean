import JGl_NumericData
import FIw_ArrayValue
set_option autoImplicit false
namespace AspisR1.JGl_NumericCanonical
open Aeneas Aeneas.Std FIq_Native
open FIw_ArrayValue (canonical cells)
open FIv_NativeValue (Canon)

theorem fromCells {N : Usize} (a : Array field.QM31 N)
    (hc : ∀ i : Fin N.val,Canon (cells a i)) : canonical a := by
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hq
  exact hc ⟨j,by simpa [a.property] using hj⟩
#print axioms fromCells
theorem high : canonical JGl_NumericData.high := by
  apply fromCells
  intro i
  fin_cases i <;>
    (change (_<2147483647 ∧ _<2147483647) ∧ (_<2147483647 ∧ _<2147483647); norm_num)
#print axioms high
theorem low : canonical JGl_NumericData.low := by
  apply fromCells
  intro i
  fin_cases i <;>
    (change (_<2147483647 ∧ _<2147483647) ∧ (_<2147483647 ∧ _<2147483647); norm_num)
#print axioms low
theorem a : canonical JGl_NumericData.a := by
  apply fromCells
  intro i
  fin_cases i <;>
    (change (_<2147483647 ∧ _<2147483647) ∧ (_<2147483647 ∧ _<2147483647); norm_num)
#print axioms a
theorem b : canonical JGl_NumericData.b := by
  apply fromCells
  intro i
  fin_cases i <;>
    (change (_<2147483647 ∧ _<2147483647) ∧ (_<2147483647 ∧ _<2147483647); norm_num)
#print axioms b
theorem c : canonical JGl_NumericData.c := by
  apply fromCells
  intro i
  fin_cases i <;>
    (change (_<2147483647 ∧ _<2147483647) ∧ (_<2147483647 ∧ _<2147483647); norm_num)
#print axioms c
theorem semantic : canonical JGl_NumericData.semantic := by
  apply fromCells
  intro i
  fin_cases i <;>
    (change (_<2147483647 ∧ _<2147483647) ∧ (_<2147483647 ∧ _<2147483647); norm_num)
#print axioms semantic
theorem poseidon : canonical JGl_NumericData.poseidon := by
  apply fromCells
  intro i
  fin_cases i <;>
    (change (_<2147483647 ∧ _<2147483647) ∧ (_<2147483647 ∧ _<2147483647); norm_num)
#print axioms poseidon
theorem internal : canonical JGl_NumericData.internal := by
  apply fromCells
  intro i
  fin_cases i <;>
    (change (_<2147483647 ∧ _<2147483647) ∧ (_<2147483647 ∧ _<2147483647); norm_num)
#print axioms internal
theorem leading : canonical JGl_NumericData.leading := by
  apply fromCells
  intro i
  fin_cases i <;>
    (change (_<2147483647 ∧ _<2147483647) ∧ (_<2147483647 ∧ _<2147483647); norm_num)
#print axioms leading
theorem full : canonical JGl_NumericData.full := by
  apply fromCells
  intro i
  fin_cases i <;>
    (change (_<2147483647 ∧ _<2147483647) ∧ (_<2147483647 ∧ _<2147483647); norm_num)
#print axioms full
theorem copy : canonical JGl_NumericData.copy := by
  apply fromCells
  intro i
  fin_cases i <;>
    (change (_<2147483647 ∧ _<2147483647) ∧ (_<2147483647 ∧ _<2147483647); norm_num)
#print axioms copy
theorem block : canonical JGl_NumericData.block := by
  apply fromCells
  intro i
  fin_cases i <;>
    (change (_<2147483647 ∧ _<2147483647) ∧ (_<2147483647 ∧ _<2147483647); norm_num)
#print axioms block
end AspisR1.JGl_NumericCanonical
