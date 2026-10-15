# Candidate parser P3 cost gate

This is the single authorized local LiteSVM transfer gate run with the candidate parser SBF and full OS mask entropy. The expected-success stage-one simulation failed with `InstructionError(3, ComputationalBudgetExceeded)`. Its log reports the verifier consumed 1,399,494 of 1,399,550 available units through `r1:query:10`, leaving 56 before the next operation. No terminal transaction ran and the run produced no success evidence JSON, so there is no completed stage-one or stage-two CU result.

The baseline full-mask P3 run is linked in `manifest.json`: stage one used 1,390,049 CU and terminal used 1,293,584 CU under a 1.4M limit. The candidate run used the same pool and registry ELFs, driver, `pool-adapter,private-leaf-salts` configuration, 13 pairs, v0 transaction format, and OS entropy mode; only the verifier SBF differs. See `input-pins.txt` and the resource record for exact hashes, command, and scope.

The task directory generated local LiteSVM key files. They remain on NUC with mode 0600; their contents were not copied into this evidence bundle, and no cleanup was performed. No live network or funded account was involved.
