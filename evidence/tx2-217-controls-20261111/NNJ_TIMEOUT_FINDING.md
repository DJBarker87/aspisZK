# NNJ_K009 timed out; no control credit

The symbolic-index `NNJ_assign_stub` shape timed out at90s (outer92.5906489559s, peak3336224KiB,swap0). It had no Failed Checks semantic verdict and is not an expected failure. No timeout/cap increase or unchanged retry.

The contract's generated pre-state capture/havoc/postcondition combines dynamic node[j] indexing before and after whole-array havoc. Replacement isolates j=0 and compares cell1 in the same named real/stub callers. This is a strict subset of the legal own-input domain and is sufficient for an existential unimplied-assertion fidelity counterexample; it is not a new precondition on the actual decoder or its native iteration. Actual NMX_assign remains unchanged and still has its arbitrary-j positive/inverted proof_for_contract pair (K006/K007). The original arbitrary-j caller timeout remains retained and retired. A second timeout of the fixed-index class would retire that class; no rename to change a verdict.


## Final disposition

NNJ_K012 fixed-index version also timed out90s (outer92.7106366800s,3187240KiB,swap0). Digest-postcondition family retired after these two attempts. NNJ_K015 tests a distinct additive minimal callee: same complete signature, input domain and footprint, but ensures only result.is_ok and writes one constant digest cell. Contract and real body pass(K013/K014); its stub caller ALSO times out90s (outer92.5134663130s,3440360KiB,swap0). The original native function and both retired caller variants remain retained unchanged; no harness was renamed to obtain a different verdict.

The observations rule out only the initial speculation that symbolic index selection alone explains the expense: fixed-index and minimal postcondition both remain expensive. The actual internal cause is NOT established. What remains is the missing semantic assertion failure under stub_verified for the Result/unit plus mutable digest-array interface. No solver timeout or compiler failure supplies it. Further Kani needs a new budget and a materially different isolated shape; no unchanged rerun or larger timeout/cap is proposed. There is no remaining authorized Lean-only obligation in this controls-only job.
