import R1Z.PV_RDB2C_PV_B2_C_Table
set_option autoImplicit false
namespace PV_B2_C_TableRange
open Aeneas Aeneas.Std PV_B2_C_Table
theorem chunk0_range : chunk0.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk0_range
theorem chunk1_range : chunk1.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk1_range
theorem chunk2_range : chunk2.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk2_range
theorem chunk3_range : chunk3.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk3_range
theorem chunk4_range : chunk4.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk4_range
theorem chunk5_range : chunk5.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk5_range
theorem chunk6_range : chunk6.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk6_range
theorem chunk7_range : chunk7.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk7_range
theorem chunk8_range : chunk8.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk8_range
theorem chunk9_range : chunk9.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk9_range
theorem chunk10_range : chunk10.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk10_range
theorem chunk11_range : chunk11.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk11_range
theorem chunk12_range : chunk12.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk12_range
theorem chunk13_range : chunk13.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk13_range
theorem chunk14_range : chunk14.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk14_range
theorem chunk15_range : chunk15.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk15_range
theorem chunk16_range : chunk16.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk16_range
theorem chunk17_range : chunk17.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk17_range
theorem chunk18_range : chunk18.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk18_range
theorem chunk19_range : chunk19.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk19_range
theorem chunk20_range : chunk20.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk20_range
theorem chunk21_range : chunk21.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk21_range
theorem chunk22_range : chunk22.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk22_range
theorem chunk23_range : chunk23.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk23_range
theorem chunk24_range : chunk24.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk24_range
theorem chunk25_range : chunk25.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk25_range
theorem chunk26_range : chunk26.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk26_range
theorem chunk27_range : chunk27.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk27_range
theorem chunk28_range : chunk28.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk28_range
theorem chunk29_range : chunk29.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk29_range
theorem chunk30_range : chunk30.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk30_range
theorem chunk31_range : chunk31.all (fun x => decide (x.val < 1024)) = true := by decide
#print axioms chunk31_range

/-- A symbolic composition over named 32-entry proofs, no large-type enumeration. -/
theorem values_range : values.all (fun x => decide (x.val < 1024)) = true := by
  simp only [values,List.all_append,chunk0_range,chunk1_range,chunk2_range,chunk3_range,chunk4_range,chunk5_range,chunk6_range,chunk7_range,chunk8_range,chunk9_range,chunk10_range,chunk11_range,chunk12_range,chunk13_range,chunk14_range,chunk15_range,chunk16_range,chunk17_range,chunk18_range,chunk19_range,chunk20_range,chunk21_range,chunk22_range,chunk23_range,chunk24_range,chunk25_range,chunk26_range,chunk27_range,chunk28_range,chunk29_range,chunk30_range,chunk31_range,Bool.and_self]

theorem member_bound (x : U16) (hx : x ∈ values) : x.val < 1024 := by
  have h : decide (x.val < 1024) = true := (List.all_eq_true.mp values_range) x hx
  exact of_decide_eq_true h

/-- Valid reads return a bounded row without reducing the full table. -/
theorem read_range (j : Usize) (hj : j.val < (1024#usize).val) :
    ∃ x : U16, Array.index_usize table j = Result.ok x ∧ x.val < 1024 := by
  obtain ⟨x,hx,hv⟩ := WP.spec_imp_exists (Array.index_usize_spec table j (by
    change j.val < table.val.length
    simpa only [table.property] using hj))
  have hm : x ∈ table.val := by
    rw [hv]
    exact List.getElem_mem _
  exact ⟨x,hx,member_bound x hm⟩

#print axioms member_bound
#print axioms read_range
#print axioms values_range
end PV_B2_C_TableRange
