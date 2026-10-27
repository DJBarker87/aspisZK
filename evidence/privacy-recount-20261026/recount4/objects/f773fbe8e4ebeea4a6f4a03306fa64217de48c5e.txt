# Fixture shape correction

Run 1 (timeout, no successful check) fixed second_occupancy_inverse=1. The actual two_outputs constructor uses the inverse of second_commitment[7]=1020. Before run 3, the input was generalized to arbitrary inverse words, covering the actual inverse. No proof from run 1 is credited as fixture coverage.

For the next split gate, allow 1800 seconds without changing Kani flags or caps. Expected work: compilation then CBMC over the actual double 21-step empty-root computation. The 21 single-step source certificate gates (including prior runjoin11 roots 18,19) establish legitimate finite predecessor work; no memory cap is raised. Source/target is changed from the timed-out whole-record assertion. Review scope at ten minutes.
