# Findings

F1: Ruling (ad) says 28 term iterations; frozen four_dots_one and its emitted body use start..min(start+4,26), hence widths [4,4,4,4,4,4,2], total 26. The proof targets that exact source sequence. No release source or control-flow model is changed.
