# NNJ_K009 timed out; no control credit

The symbolic-index `NNJ_assign_stub` shape timed out at90s (outer92.5906489559s, peak3336224KiB,swap0). It had no Failed Checks semantic verdict and is not an expected failure. No timeout/cap increase or unchanged retry.

The contract's generated pre-state capture/havoc/postcondition combines dynamic node[j] indexing before and after whole-array havoc. Replacement isolates j=0 and compares cell1 in the same named real/stub callers. This is a strict subset of the legal own-input domain and is sufficient for an existential unimplied-assertion fidelity counterexample; it is not a new precondition on the actual decoder or its native iteration. Actual NMX_assign remains unchanged and still has its arbitrary-j positive/inverted proof_for_contract pair (K006/K007). The original arbitrary-j caller timeout remains retained and retired. A second timeout of the fixed-index class would retire that class; no rename to change a verdict.
