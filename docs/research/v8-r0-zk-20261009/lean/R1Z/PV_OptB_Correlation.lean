import R1Z.PV_OptB_JointTransport
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_Correlation
open R0Z R0Z.FsGood R0Z.FsAbort PV_OptB_JointTransport

/-- Tiny logical diagnostic only: this is NOT an admitted native witness
counterexample and does not trigger the option-A stop condition. -/
def left (b : Bool) : ℚ := if b then 1 else 0
def right (b : Bool) : ℚ := if b then 0 else 1
def signal (b : Bool) : Option Unit := if b then some () else none

theorem old_equal_means : mean left = mean right := by
  norm_num [mean,left,right,Fintype.sum_bool]

#print axioms old_equal_means
theorem left_overlay_mean : mean (overlay signal left (fun _ => (0 : ℚ))) = 0 := by
  norm_num [mean,overlay,signal,left,Fintype.sum_bool]

#print axioms left_overlay_mean
theorem right_overlay_mean : mean (overlay signal right (fun _ => (0 : ℚ))) = 1 / 2 := by
  norm_num [mean,overlay,signal,right,Fintype.sum_bool]

#print axioms right_overlay_mean
/-- Equal old means and one common failure signal do not imply equal
new means. This finite logical example is not a native counterexample. -/
theorem old_marginal_is_insufficient :
    mean left = mean right ∧
      mean (overlay signal left (fun _ => (0 : ℚ))) ≠
        mean (overlay signal right (fun _ => (0 : ℚ))) := by
  refine ⟨old_equal_means, ?_⟩
  rw [left_overlay_mean,right_overlay_mean]
  norm_num

#print axioms old_marginal_is_insufficient
end R1Z.PV_OptB_Correlation
