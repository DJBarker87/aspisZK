# Forward canonicality on retained bytes: leading three regions

JFz_Scan00/01/02.canonical_selected establish the three leading scan predicates
on the exact retained proof, at offsets 7031/7495/7783 and lengths 464/256/2272.
Each selected range is joined from kernel-checked 32-byte literal associations;
canonicality is proved one four-byte word at a time. All checked declarations
use only standard axioms. Generic concatenation/slicing is JFz_CanonicalAppend.

Validation: JFz_004 through 007 passed. JFz_007, the largest region: exit 0,
105.90493430400966 seconds, capped at High6G/Max8G/Swap0/Tasks64, -M7000.
Full per-attempt source/dependency/revision/time/RSS/swap/axiom receipts retained.
JFz_002 failed on literal-list recursion depth; it was replaced with named
32-byte selection leaves and symbolic joins. JFz_003 failed on map/append
conversion; JFz_004 explicitly uses List.map_append. No limit was raised.
No timed-out or killed job has been rerun. The shell batch's decimal-formatting
error attempted to read nonexistent JFz_000.json, before Lean; it was corrected
without repeating any compiled module.

Host admission succeeded after aggregate-refusal retries 1–4 and the required
waits; one scope now carries sequential one-file invocations. No other job's
scope was modified. The new results are partial forward parsing facts, not the
full joint accepted fixture. No top theorem premise removal is claimed.
