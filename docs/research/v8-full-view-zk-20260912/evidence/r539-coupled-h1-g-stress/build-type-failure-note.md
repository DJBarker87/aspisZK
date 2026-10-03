# Earlier aggregate helper compile failure receipt

Service: `run-u777.service`, an earlier capped optimized build attempt. It exited 101 after 27.0 seconds, max reported process RSS 594,148 KiB and zero swap. The compiled helper was `.r21-scratch/r117-joint-privacy-stress/r17_c1_witness_audit.rs`, SHA-256 `699a038898ed9bd4528a9861549b2d6f861e05da142aa49c5af246bfad5743dd` (that path was subsequently overwritten and no byte-exact source copy remains).

The captured tool output showed E0308 mismatches where the `r17_coupled_audit::dot` helper over `QM31` was applied to M31 matrix/solution values at helper lines 348, 377, 393 and 486. The corrected retained source uses a local M31 dot for those four checks. The full compiler stderr was not saved; this note reports only the error details present in the execution output. The failed build did not run the solver.
