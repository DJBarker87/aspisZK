import PV_B3_Copy_117_Funs
import PV_B3_Result
namespace PV_B3_Range117
open Aeneas Aeneas.Std Result PV_B3_Copy_117
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31
abbrev Coefficients := Array Q 27#usize

def selectedIndices : List Usize := [0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize, 9#usize, 10#usize, 11#usize, 12#usize, 13#usize, 14#usize, 15#usize]

def maskIndices : List Usize := [0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize, 9#usize]

def hornerIndices : List Usize := [25#usize, 24#usize, 23#usize, 22#usize, 21#usize, 20#usize, 19#usize, 18#usize, 17#usize, 16#usize, 15#usize, 14#usize, 13#usize, 12#usize, 11#usize, 10#usize, 9#usize, 8#usize, 7#usize, 6#usize, 5#usize, 4#usize, 3#usize, 2#usize, 1#usize, 0#usize]

theorem selected_order : selectedIndices.map (fun i => i.val) = List.range 16 := rfl
theorem mask_order : maskIndices.map (fun i => i.val) = List.range 10 := rfl
theorem horner_order : hornerIndices.map (fun i => i.val) = (List.range 26).reverse := rfl

def scatter {n : Usize} (input : Array Q n) (exponents : Array U8 n) :
    List Usize → Coefficients → Result Coefficients
  | [], coefficients => ok coefficients
  | column::rest, coefficients => do
    let q ← Array.index_usize input column
    let coordinate ← lift (column &&& 3#usize)
    let value ← host_arithmetic.mul_tower_basis q coordinate
    let exponent ← Array.index_usize exponents column
    let index ← lift (UScalar.cast .Usize exponent)
    let next ← Array.update coefficients index value
    scatter input exponents rest next

def horner (coefficients : Coefficients)
    (prepared : host_arithmetic.PreparedQm31Multiplier) : List Usize → Q → Result Q
  | [], shared => ok shared
  | exponent::rest, shared => do
    let product ← host_arithmetic.PreparedQm31Multiplier.mul prepared shared
    let q ← Array.index_usize coefficients exponent
    let next ← aspis_core.field.QM31.add product q
    horner coefficients prepared rest next

theorem selected (c1 : Array Q 16#usize) :
    host_arithmetic.selected_coefficients c1 =
      scatter c1 host_arithmetic.FACTOR_EXPONENTS selectedIndices
        (Array.repeat 27#usize aspis_core.field.QM31.ZERO) := by
  unfold host_arithmetic.selected_coefficients selectedIndices
  simp only [scatter, PV_B3_Result.bind_assoc, bind_tc_ok]

theorem mask_only (coefficients : Coefficients) (mask : Array Q 10#usize) :
    host_arithmetic.mask_only_coefficients coefficients mask =
      scatter mask host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS maskIndices coefficients := by
  unfold host_arithmetic.mask_only_coefficients maskIndices
  simp only [scatter, PV_B3_Result.bind_assoc, bind_tc_ok]

theorem prepared_horner (coefficients : Coefficients) (linear : Q) :
    host_arithmetic.selected_horner coefficients linear =
      (do
        let prepared ← host_arithmetic.PreparedQm31Multiplier.new linear
        let shared ← Array.index_usize coefficients
          aspis_core.state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE
        horner coefficients prepared hornerIndices shared) := by
  unfold host_arithmetic.selected_horner hornerIndices
  simp only [horner, PV_B3_Result.bind_assoc, bind_tc_ok]

#print axioms selectedIndices
#print axioms maskIndices
#print axioms hornerIndices
#print axioms selected_order
#print axioms mask_order
#print axioms horner_order
#print axioms scatter
#print axioms horner
#print axioms selected
#print axioms mask_only
#print axioms prepared_horner
end PV_B3_Range117
