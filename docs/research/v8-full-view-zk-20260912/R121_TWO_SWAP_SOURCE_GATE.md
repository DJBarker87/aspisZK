# R121: two-swap source weights and fixed-query polynomial

Source base: `1cf29982431cc456ec7d0b670b6c221366e557b4`.
Selected native manifest: `26755a4250ec6075005e840565040414b694deb97fb1830fc95aff2692d34fb6`.

The new exact-field source chain compiles: for every permitted fixed tuple of
22 distinct query roots excluding 1, its determinant polynomial is nonzero
and has total degree at most **819**. This is the two-swap profile's own
certificate, not reuse of the old T163 ordering or its nonzero theorem.

No verifier, proof format, challenge, mask, or validation path changed.
The measured endpoint remains **999,790 / 999,532 CU under the actual 1M cap**.
Only 210 CU margin remains on the larger fixture. No new SBF run or universal
resource bound is claimed. **Full privacy and soundness remain unproved.**

## Exact proved boundary

- `TwoSwapSourceTable`: the signed-bit permutation's inverse is proved by
  digit arithmetic, followed by both source swaps, `(127,1023)` and
  `(126,1021)`. The pivot is fixed; the first 89 pad images and the 131-entry
  residual restriction agree with the retained certificate.
- `TwoSwapSourceWeights`: arbitrary-ring/challenge dual weights agree with
  the full source-shaped chord transpose on the 128 quotient coordinates.
  All 131 chord outputs are retained. The complete 256-block coefficient
  calculation restricts to 32 blocks for every coefficient. Image updates
  remain in the source expression and disappear only by the proved support
  restriction, not by assuming arbitrary image residuals are zero.
- `TwoSwapSourceG`: the literal ordered scatter retains all 271 coins.
  Its low restriction depends on the final coin-0 write, while the other
  270 values remain arbitrary. Both original-weight channels, including
  the inactive indicator and balancing pivot, have exact decompositions.
- `TwoSwapSourceFixed` and `TwoSwapSourceMinor`: the R120 numeric certificate
  is a specialization of these new weights, transported through a base-field
  homomorphism. Three point observations and all seven coefficients of each
  channel are included. The source-shaped minor equals R120's invertible
  normalized matrix for every permitted fixed root tuple, arbitrary previous
  coin values and arbitrary image challenge tau.
- `TwoSwapResidualModel/Source/Polynomial/Degree/Nonzero`: the arbitrary-
  challenge source-shaped map equals the newly instantiated polynomial map.
  Query-section coefficients are fixed parameters; fourteen challenge
  coordinates are active. The entry degree is at most 63 and the determinant
  degree at most 819. The new fixed assignment proves nonvanishing, including
  an explicit theorem over the exact QM31 tower.
- `TwoSwapChordScale` and `TwoSwapSourceGate`: the rational chord determinant
  equals the normalized determinant times its thirteenth-power scale.
  The nonsingularity equivalence retains nonzero denominators and distinct
  chord parameters. It does not discard degenerate source events.

The algebraic witness is not asserted to be a sampled Fiat--Shamir prefix.
These are exact-field, source-shaped statements, not complete Rust/SBF
machine-word refinement or a certified compiler result.

## Source and replay evidence

The literal audit compares all 1,024 permutation entries, all 1,024 inverse
entries, and all 1,024 inactive flags against the selected source pins. Only
the unchanged inactive inventory is reused from `T163SourceTable`; its
ordering is not. All 89 pad images and the 131-entry low table match. The
one-swap negative differs at two positions; the old ordering differs at 1,023.
The collector additionally verifies every selected native source-file pin.

The single final frozen replay compiles **12 changed targets**, with
**76 clean `#print axioms` audits**. All exit 0; only `propext`,
`Classical.choice`, and `Quot.sound` are reported. Per-target wall times total
**18.01 seconds**; maximum per-target RSS is **2,464,044 KiB**, with **zero
swaps**. Exact commands, revisions, source hashes, metrics and audit output
are in the [receipt](evidence/r121-two-swap-source/receipt.json).

Every focused compile and the final replay uses the existing Lean 4.32.0
cache, `lake env lean -j1 -M4500`, and a 5/7 GiB zero-swap cgroup. No dependency
rebuild or large recurrence normalization was needed. The 42 unchanged R120
leaves were not recompiled. The inherited runner's older field-extraction
audit is a cache/dependency check, not proof of current optimized word code.

Eight failed preflights are retained: one upload race and seven local Lean
elaboration failures. The digit inverse received explicit division identities;
the flattening proof was generalized symbolically to rings; function and
finite-index rewrites were made explicit. No memory cap was raised, and no
failed proof was used as a premise. Public logs only are collected: no private
fixture, wallet key or compiled object.

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/check_r121_evidence.py
```

The Solana testing/security skill kept canonical decoding, authentication and
rejection behavior outside this proof-only change. No unchanged runtime suite
was repeated and no transaction was submitted.

## First remaining proposition

Justify the exceptional-event law for this polynomial in the **actual
adaptive shared-oracle accepted-prefix experiment**, including the source
premises. Query roots can depend on earlier challenges and disclosed messages.
A nonzero polynomial for every *fixed* root tuple does not justify treating
those earlier challenges as independent after conditioning on future roots.
No numerical privacy advantage is claimed from the degree-819 result alone.

This closes one algebraic G-residual step, not universal joint C1/H1/G
affine-image compatibility. That larger obligation still includes p0/p2 and
all retained semantic, point, raw, final and relation observations. Causal
posterior simulation, seed/C2/eight-way commitment composition, visible
failures/retries/publication, coherent pre-beta quotient-pair extraction,
soundness loss accounting and implementation refinement remain open.
The active under-1M-then-full-security goal is not complete.
