# Fresh attempt bound focused evidence

The green target `R1FreshAttemptBound` defines an adaptive sequence of 33 row attempts. For each row, the message selector and table update are explicit functions of the current prefix/table and prior sampler view. The row sampler is interpreted with fresh independent answers. The theorem gives `hitMass_le` from a per-row density premise and derives `thirty_three_hitMass_lt` from the supplied per-attempt envelope.

The scope is deliberately limited: this is not the memoized/shared random-oracle experiment, and it does not include hidden retries. The numerical `< 2^-100` result is conditional on the stated density premise for every reachable prefix, message, and table. It does not establish that premise or source correspondence.

A related old theorem, `adaptiveFailureProbabilityFromStart_le_attempts_mul`, handles adaptive bad sets over uniform single answers and prior histories. It is an analogue, not a direct replacement for this row-program interface. `mean_firstHit_union_le` is only a union bound over a finite index set on one common sample. These relationships and hashes are recorded in the manifest.

Source base: `8e6c2b4cba1c54fe165f7436f5fc3ada1e1ae0f3`. Attempts a–c failed (a timed out; b/c proof plumbing); attempt d is green. Receipt d records exit 0, 2.16 seconds, peak RSS 3,608,080 KiB, zero swap, and a 4 GiB high / 6 GiB maximum / zero-swap / 128-task cap. Both public theorems have only standard axioms `[propext, Classical.choice, Quot.sound]`. Exact snapshots, receipts, logs, sidecars, source pins, runner and environment are retained. The object archive contains the final target object only.
