# Failing attempts

NKG_K010: own source fission introduced overlapping mutable borrows by nesting both log calls. Compiler failure, no native credit. Replacement K013 stores the first reply in a local, preserving original Rust evaluation order. K013 passed; K011/K012 semantic controls failed. No shared infrastructure changed.

NKG_K020: unexpected positive failure, 1/822 checks at core panicking assert_failed_inner, 34.082582716s wall, 1766960KiB peak RSS, zero swaps. Prepared-stage structured Eq assertion has no credit. Replacement K032 keeps the SAME harness name and checks an arbitrary raw cache word (nine-word complete-record extensional assertion), with controls K033/K034. The verdict is not renamed or reclassified. Diagnosis remains pending; no shipped-code bug claimed.

Lean L003/L005/L006/L009/L013 were local elaboration failures (numeral coercions/array-length reduction and table Fin indices). Every replacement changed source; failed objects/diagnostic sorryAx are excluded from accepted roots.

K032 PASS with K033/K034 FAIL establishes raw nine-word prepared-cache forwarding under the SAME NKG_prepared_stage harness name, replacing the structured equality assertion with an arbitrary-coordinate raw-content assertion. K020 remains an excluded diagnostic; no claim about its derived Eq implementation is made.

K023 NKG_group_iteration TIMEOUT (98.919297326s wall, 2118508KiB peak RSS, zero swaps; fixed solver deadline90s), no credit. Controls K024/K025 were cancelled without launch. Replacement: source-ordered pack, subtraction, prepared-sum and final-multiply segments, each on arbitrary pre-state with full typed child replies, native controls and Lean frame composition. No cap/timeout increase or unchanged rerun.

L034 stopped at the symbolic group association's chained rw (maximum recursion depth), not a failed field identity. No limit was raised. L035 replaces that rewrite with named differences and explicit congruence steps, keeping all field models symbolic.

L047 was submitted and completed before the owned client failed constructing its binary-safe collector f-string (unescaped nested dictionary braces). The collector was repaired without changing validation, and the existing L047 receipt/sources/output were recovered READ-ONLY by NKG_recover.py. No compile was resubmitted; the recovered actual exit and resources remain authoritative.

Finalizer repairs before output: recognize an explicitly suffixed compressed predecessor manifest; replace the mistaken assumption of a standalone CLOSED PreparedQm31Multiplier::mul row with the explicit field-product-rule-A supplement (see NKG_FINDINGS.md). No original ledger row was changed. The local validator now passes all exact baseline/receipt/source/audit comparisons. L055 pin/export/retention scope passed; it is not a second combined audit.

Own final local manifest validator initially demanded an axiom-print directive even in structure-only cut modules with no theorem. Its check now applies to modules declaring theorems; all actual theorem roots remain in the47-root raw audit. No proof or audit criterion was relaxed.
