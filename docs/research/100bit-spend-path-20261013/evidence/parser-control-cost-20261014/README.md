# Controlled baseline-source P3 gate with reused OS proof

This single gate used the baseline-source control SBF, existing P3 pool/registry ELFs, and the exact proof/public inputs from the candidate run that failed stage one. Inputs were SHA-pinned before execution. The gate exited 1 with `ComputationalBudgetExceeded` at stage one after logging 1,399,494 of 1,399,550 available compute units through `r1:query:10`; 56 units remained before the next operation. No terminal stage ran and no success evidence JSON was produced.

The complete run log and resource receipt are retained. The proof and public bytes used and emitted by the reuse path are retained and hash-identical. The command omitted `--mask-entropy os` because it used the explicit `--reuse` inputs, so this run draws no new mask; it replays the prior full-OS proof/public artifacts.

The local LiteSVM task generated fresh local key files. They remain on NUC with mode 0600; their secret contents are not in this bundle and no cleanup was performed. No network or funded account was involved.
