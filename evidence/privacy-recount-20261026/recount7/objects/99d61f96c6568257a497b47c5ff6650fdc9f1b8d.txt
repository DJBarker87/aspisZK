import PV_B3_AuditSourceD324
import PV_B3_SparseArray
namespace PV_B3_ZeroArithmetic
open Aeneas Aeneas.Std Result PV_B3_Copy_117
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31
abbrev Z := aspis_core.field.QM31.ZERO
abbrev O := aspis_core.field.QM31.ONE
-- Only tiny field leaves are reduced. Traversals use these named equations.
theorem add : aspis_core.field.QM31.add Z Z = ok Z := by with_unfolding_all rfl
theorem mul : aspis_core.field.QM31.mul Z Z = ok Z := by with_unfolding_all rfl
theorem one_mul : aspis_core.field.QM31.mul O Z = ok Z := by with_unfolding_all rfl
theorem one_add : aspis_core.field.QM31.add O Z = ok O := by with_unfolding_all rfl
theorem square : aspis_core.field.QM31.square Z = ok Z := by with_unfolding_all rfl
theorem scale3 : aspis_core.field.QM31.mul_m31 Z 3#u32 = ok Z := by with_unfolding_all rfl
theorem scale22 : aspis_core.field.QM31.mul_m31 Z 22#u32 = ok Z := by with_unfolding_all rfl
theorem scale275 : aspis_core.field.QM31.mul_m31 Z 275#u32 = ok Z := by with_unfolding_all rfl
theorem scale150 : aspis_core.field.QM31.mul_m31 Z 150#u32 = ok Z := by with_unfolding_all rfl

def prepared : host_arithmetic.PreparedQm31Multiplier :=
  ⟨Array.repeat 3#usize (Array.repeat 3#usize 0#u32)⟩
theorem prepare : host_arithmetic.PreparedQm31Multiplier.new Z = ok prepared := by
  with_unfolding_all rfl

theorem index_repeat {A : Type} (n : Usize) (x : A) (i : Usize) (h : i.val < n.val) :
    Array.index_usize (Array.repeat n x) i = ok x := by
  rw [← PV_B3_SparseArray.constant]
  exact PV_B3_SparseArray.index n (fun _ => x) i h

theorem update_repeat {A : Type} (n : Usize) (x : A) (i : Usize) (h : i.val < n.val) :
    Array.update (Array.repeat n x) i x = ok (Array.repeat n x) := by
  rw [← PV_B3_SparseArray.constant]
  rw [PV_B3_SparseArray.update n (fun _ => x) i h x]
  have he : Function.update (fun _ : Nat => x) i.val x = (fun _ : Nat => x) := by
    funext k
    by_cases hk : k = i.val
    · subst k; rw [Function.update_self]
    · rw [Function.update_of_ne hk]
  rw [he]

abbrev CZero : aspis_core.field.CM31 := ⟨0#u32,0#u32⟩
theorem component_zero : host_arithmetic.prepared_component_mul (Array.repeat 3#usize 0#u32) CZero = ok CZero := by
  with_unfolding_all rfl
theorem cadd_zero : aspis_core.field.CM31.add CZero CZero = ok CZero := by with_unfolding_all rfl
theorem csub_zero : aspis_core.field.CM31.sub CZero CZero = ok CZero := by with_unfolding_all rfl
theorem hostr_zero : host_arithmetic.cm31_mul_r CZero = ok CZero := by with_unfolding_all rfl

theorem prepared_mul : host_arithmetic.PreparedQm31Multiplier.mul prepared Z = ok Z := by
  simp (disch := decide) only [host_arithmetic.PreparedQm31Multiplier.mul,
    prepared,aspis_core.field.QM31.ZERO,index_repeat,component_zero,cadd_zero,csub_zero,hostr_zero,bind_tc_ok]

#print axioms component_zero
#print axioms cadd_zero
#print axioms csub_zero
#print axioms hostr_zero
#print axioms add
#print axioms mul
#print axioms one_mul
#print axioms one_add
#print axioms square
#print axioms scale3
#print axioms scale22
#print axioms scale275
#print axioms scale150
#print axioms prepare
#print axioms prepared_mul
#print axioms index_repeat
#print axioms update_repeat
end PV_B3_ZeroArithmetic
