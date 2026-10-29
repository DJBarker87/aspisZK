# Header reference tag mismatch

The exploratory E015 reference header_gate accepts transition tags 0/1. Frozen historical_anchor.rs::PoolV1TransitionKind uses 1/2, and pair_forest_terminal.rs::transition_kind rejects every other tag. E015 therefore has NO source/cohort credit. This is a lane reference error, not a frozen implementation or Kani defect. It had been marked unassociated, never CLOSED.

The original source and extraction remain immutable. The separate request_gate native candidate uses 1/2. Its new extraction is OPEN because all 20 extraction runs have been consumed; no extra run or relabel is authorized. A native counterexample and focused Lean discrepancy facts are scheduled. Matching positive/control windows for the corrected candidate will remain component evidence, without four-part closure.

Final status: K069 failed compilation before verification. There is NO retained native counterexample from this lane. L076 establishes only the bad extraction accepts zero; the actual 1/2 definition is supported by frozen Rust inspection. The corrected native candidate and extraction remain OPEN.
