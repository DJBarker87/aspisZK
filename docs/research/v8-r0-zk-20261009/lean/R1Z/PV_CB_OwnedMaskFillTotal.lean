import R1Z.PV_CB_OwnedMaskFill
import R1Z.PV_CB_ForwardTotal
import R1Z.ProverRwSuccessPointsTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_OwnedMaskFillTotal
open Aeneas Aeneas.Std Result ProverRwSuccessArithmeticTotal PV_CB_OwnedMaskFill

theorem step_total {N : Usize} (data : Array Q N) (exponents : Array Usize N)
    (safe : ∀ x,x∈exponents.val → x.val<27) (i : Usize) (coeff : Coeff)
    (inside : i.val<N.val) : Total (step data exponents i coeff) := by
  have hi : i.val<exponents.val.length := by rw [exponents.property];exact inside
  let e := exponents.val[i.val]
  have he : Array.index_usize exponents i=.ok e := ProverCommitArrayIndex25.array_index_usize_ok _ _ inside
  have bound : e.val<27 := safe e (List.get_mem _ ⟨i.val,hi⟩)
  unfold step
  rw [he]
  simp only [bind_tc_ok,lift]
  apply bind_total (ProverRwP6ArrayRead.read data i inside);intro q
  apply bind_total (PV_CB_OwnedMaskLeaves.tower_total q _ (PV_CB_MaskIndices.coordinate i));intro v
  exact ProverRwSuccessPointsTotal.update_total coeff e v bound

theorem c1_safe (x : Usize) (h : x∈c1Exponents.val) : x.val<27 := by
  simp only [c1Exponents,Array.make,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
theorem mask_safe (x : Usize) (h : x∈maskExponents.val) : x.val<27 := by
  simp only [maskExponents,Array.make,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem c1 (data : Array Q 16#usize) (coeff : Coeff) :
    Total (PV_CB_OwnedMask.owned.fill_c1 data coeff 0#usize) := by
  rw [PV_CB_OwnedMaskFill.c1 data 16 0#usize coeff (by decide)]
  exact PV_CB_ForwardTotal.finite_total (step data c1Exponents) 16#usize
    (fun i hi c => step_total data c1Exponents c1_safe i c hi) 16 0#usize coeff (by decide)
theorem mask (data : Array Q 10#usize) (coeff : Coeff) :
    Total (PV_CB_OwnedMask.owned.fill_mask data coeff 0#usize) := by
  rw [PV_CB_OwnedMaskFill.mask data 10 0#usize coeff (by decide)]
  exact PV_CB_ForwardTotal.finite_total (step data maskExponents) 10#usize
    (fun i hi c => step_total data maskExponents mask_safe i c hi) 10 0#usize coeff (by decide)
#print axioms step_total
#print axioms c1_safe
#print axioms mask_safe
#print axioms c1
#print axioms mask
end R1Z.PV_CB_OwnedMaskFillTotal
