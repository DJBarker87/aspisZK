from step import check,append
m='R1Z/PV_OptB_Correlation';ns='R1Z.PV_OptB_Correlation'
check(m)
append(m,ns,'left_overlay_mean','''theorem left_overlay_mean : mean (overlay signal left (fun _ => (0 : ℚ))) = 0 := by
  norm_num [mean,overlay,signal,left,Fintype.sum_bool]
''')
append(m,ns,'right_overlay_mean','''theorem right_overlay_mean : mean (overlay signal right (fun _ => (0 : ℚ))) = 1 / 2 := by
  norm_num [mean,overlay,signal,right,Fintype.sum_bool]
''')
append(m,ns,'old_marginal_is_insufficient','''/-- Equal old means and one common failure signal do not imply equal
new means. This finite logical example is not a native counterexample. -/
theorem old_marginal_is_insufficient :
    mean left = mean right ∧
      mean (overlay signal left (fun _ => (0 : ℚ))) ≠
        mean (overlay signal right (fun _ => (0 : ℚ))) := by
  refine ⟨old_equal_means, ?_⟩
  rw [left_overlay_mean,right_overlay_mean]
  norm_num
''')
