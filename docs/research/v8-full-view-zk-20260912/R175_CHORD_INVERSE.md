# R175 selected chord inverse fragment

The selected generated equality functions for CM31, QM31 and SecureCirclePoint now have exact structural equality theorems. QM31 inequality also agrees exactly with structural inequality, for every raw value.

`selectedCoordinates_valid` proves the callback’s actual choice of x when the x coordinates differ, otherwise y, selects distinct canonical coordinates whenever both points are canonical and distinct. `rawChordInverse_exact` proves the selected subtraction, inverse and `Option.ok_or(Error::Domain)` fragment returns the exact encoded inverse under those premises. This rules out Domain at this fragment only after the premises have been justified.

All nine theorems compiled in the pinned capped cache: 1.56 seconds, peak RSS 3,712,408 KiB, zero swaps. Full axiom reports contain only propext, Classical.choice and Quot.sound. The [evidence manifest](evidence/r175-chord-inverse/manifest.json) retains the failed draft and the six-lemma focused predecessor.

The full freeze also computes gamma batches before inversion; this fragment theorem does not skip or certify them. Canonicality and distinctness still need to be connected to complete actual pair execution. Actual standard-library fold/extend, full callback result/error/oracle chronology through rho, privacy and soundness remain open. Verifier source, CU evidence and security parameters are unchanged; no CU or unchanged regression suite was rerun.
