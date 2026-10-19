import CuSavingsRangeTraversal
import CuSavingsRhoInputs

/-! Identify the actual Range loop's finite traversal with the previously
checked rho items, deriving bounds/unique coverage from the source iterator. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoRangeInputs
open Aeneas Aeneas.Std Result
open CuSavingsRangeTraversal
abbrev Basis := CuSavingsRhoInputs.Basis

def basisWord (basis : Basis) (i : Usize) : U32 := (basis.val[i.val]?).getD 0#u32

theorem indices_eq (length : Usize) :
    indices 0 length.val = List.ofFn (CuSavingsRhoInputs.index length) := by
  apply List.ext_getElem
  · simp only [indices,List.length_map,List.length_range',List.length_ofFn]
  · intro i hi hi'
    simp only [indices,List.getElem_map,List.getElem_range',List.getElem_ofFn,
      Nat.zero_add,Nat.one_mul]
    apply UScalar.eq_of_val_eq
    rw [word_val,CuSavingsRhoInputs.index_val]
    apply Nat.mod_eq_of_lt
    have hlen : i < length.val := by
      simpa only [List.length_ofFn] using hi'
    exact Nat.lt_trans hlen (by scalar_tac)

theorem pairs_eq (basis : Basis) (length : Usize) (hlen : length.val ≤ 256) :
    (indices 0 length.val).map (fun i => (i,basisWord basis i)) =
      CuSavingsRhoInputs.items basis length hlen := by
  rw [indices_eq]
  simp only [List.map_ofFn,CuSavingsRhoInputs.items]
  apply congrArg List.ofFn
  funext i
  apply Prod.ext rfl
  have hb : i.val < basis.val.length := by
    have hi : i.val < 256 := Nat.lt_of_lt_of_le i.isLt hlen
    simpa only [basis.property,show (256#usize).val=256 by scalar_tac] using hi
  simp only [basisWord,CuSavingsRhoInputs.index_val,List.getElem?_eq_getElem hb,
    Option.getD_some,CuSavingsRhoInputs.basisAt]

theorem indices_bound (length : Usize) (i : Usize) (hi : i ∈ indices 0 length.val) :
    i.val < length.val := by
  rw [indices_eq] at hi
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
  exact j.isLt

#print axioms indices_eq
#print axioms pairs_eq
#print axioms indices_bound
end AspisR1.CuSavingsRhoRangeInputs
