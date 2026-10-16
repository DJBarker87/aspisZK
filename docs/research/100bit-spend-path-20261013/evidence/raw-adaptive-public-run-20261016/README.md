# Actual adaptive raw-byte public recovery through round 26

`RawEarlyPublicSelection.at_first_cell` transports the checked public-free selector to actual raw-byte verifier traces, following an arbitrary consistent raw prover prefix. It uses the exact legacy verifier trace and the single raw collision exclusion. Adversarial oracle inputs remain unrestricted.

`RawEarlyPublicRun.select_actual_run` proves that the selector returns the public statement chosen by the actual adaptive prover. `adaptive_run_decodes_and_follows` combines it with the concrete table-derived commitment words and the checked decoder completion. The resulting decoder receives the current address and table, not an externally supplied public statement. This closes public selection and actual decoder completion for rows 0–26, with tag 2, validity, strict commitment parser and query/collision premises explicit.

The later rows, compiled adaptive decoder combination, terminal source correspondence, efficient extraction and final soundness claim remain open.

Focused Lean 4.32.0 NUC checks; all exits 0, process swaps 0, and printed axioms standard only. Per-target receipts retain source/import pins, cap, wall time, RSS and axiom outputs.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `RawEarlyPublicSelection` | 1.659 | 3651144 | 2 |
| `RawEarlyPublicRun` | 2.079 | 3635220 | 2 |
