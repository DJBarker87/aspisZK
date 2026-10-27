import RPt_FJi_FourValue
import Port5Q1_OpeningValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_ArrayAdapter
open Aeneas Aeneas.Std Result
open FJi_Accumulations
/-- Coordinate adapters preserve each original output VALUE, including its index. -/
theorem values (a : Array NE 4#usize) (j : Fin 4) :
    Port5Q1_OpeningValues.values (FIp_DotsAdapter.fromArray a) j=FIp_ArrayValue.value a j.val := by
  unfold Port5Q1_OpeningValues.values FIp_DotsAdapter.fromArray FIp_ArrayValue.value
  simp only [List.getElem?_map]
  cases h : a.val[j.val]? with
  | none => simp only [Option.map_none,Option.getD_none];rfl
  | some x => simp only [Option.map_some,Option.getD_some];rfl
#print axioms values
end AspisR1.FJi_ArrayAdapter
end
