# R21 review: public-arithmetic certification and a short-cycle experiment

Reviewed remote: `research/v8-r20-execution-core-20260922`,
`6f00e7f6c893c3a81bc37526e32d563434d303c8` (22 September 2026).
R20 implementation: `da2bc4808481f9450e8a048cfff3ada1cf3e28f0`.

**This bundle does not contain a sub-1M verifier.** It contains an executed
short-cycle basis experiment and a design for moving expensive *public*
arithmetic into an auxiliary computation proof. No GKR implementation,
new Aspis source execution, Rust compilation, SBF measurement or security
closure is claimed here. No repository branch was changed.

The best pushed R20 clean primary is 2,865,333 / 2,866,803 CU on two retained
R19 proofs. Its real 1M gate fails. Those are repository-reported measurements,
not measurements repeated in this environment.

## Contents

* `design/PUBLIC_ARITHMETIC.md`: concrete boundaries, security reduction,
  budget, failure modes and stop/go experiments for a helper proof.
* `design/SHORT_CYCLES.md`: exact rank-minimal permutation completion;
  same first89/pivot/support but a different protocol map.
* `tests/`: compiled finite-field model, transport tests and preliminary
  H1/G rank screens. This is NOT the complete R19 626-equation source system.
* `tools/generate_cycles.py`: exact integer signed-operator certificate;
  optionally checks the actual staged ORDER before emitting a candidate.
* `SOURCE_PINS.json`: current Git provenance and scope.

## Reproduce

```
python3 run_checks.py --ranks
python3 tools/generate_cycles.py --stage-table /path/to/r17_basis_tables.rs
```

The second command must use the actual assembled R20 stage, not an arbitrary
repository template. A mismatch fails closed. No auto-patching is performed.
The rank screens use independently parameterized circle points, not the
actual q22 sampler, and do not prove privacy or its exceptional-event law.

## Immediate engineering assignment

Keep R20 clean B as the measured control. First extract its expensive public
arithmetic into a pure reference interface, while preserving *all* source
checks. Build a proof-of-public-computation pilot for the ordinary terminal;
count and measure verifier-side input evaluation and wiring evaluation too.
Do not replace that pilot with an abstract provider assumption. If its total
verification cost does not beat the native computation convincingly, record
that failure and stop expanding it. A generic GKR implementation with linear
wiring scans may be worse than the current verifier.

The short-cycle experiment is separate and lower priority. It requires a
new profile, new genuine witness fixtures and the full C1/H1/G/R19-message
source checks. Its rank reduction is NOT a predicted CU percentage. Do not
change R20's map merely to make a microbenchmark attractive.

For the original target, final acceptance requires the complete single
verification under 1,000,000 CU with all wrappers and the supported heap.
Splitting execution across transactions is a different goal; never describe
that as reducing total verification below 1M.
