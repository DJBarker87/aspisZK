# R15 exhaustive source circle-domain check

Date: 2026-09-20; privacy branch base `198297e5`.

`crates/aspis-core/tests/r15_circle_domain.rs` calls the actual
`selected_circle_fiber_points_shared(20, ids)` for every one of the 262,144
valid fibre IDs, in reversed batches of 512. It checks:

- all 192 entries in the three 64-entry lookup tables are canonical and
  satisfy the circle equation;
- every returned point matches an independent u128 modular implementation
  of the source's three-window composition and index selection;
- every returned coordinate is canonical, both coordinates are nonzero,
  and `x²+y²=1 mod 2147483647`;
- returned length and order match the caller's ID list.

All checks passed. The integer reference does not call the Rust M31
arithmetic methods. Its largest intermediate is less than three times P²,
well below the u128 limit, and subtraction adds P² before reducing.

## Source lock and execution

The following files have no diff against selected source revision
`9e432896a4e1515efebe940b71fd9b4f9f009189`:

| File | SHA-256 |
| --- | --- |
| `crates/aspis-core/src/circle_fri.rs` | `77625499c80b30fe9de1e79daaf35dc964bf0cb675a65ced69592d3d421c856b` |
| `crates/aspis-core/src/field.rs` | `5795495e2fa9ad85e097c2ad96ffc826aaad3c16afc0e0bd00459f9f51068cd8` |
| `crates/aspis-core/build.rs` | `7905b8c2a92c72a79a8a6c785a91ce162fb338569a02867f671d1910e21b6e0d` |

Command, using the existing release cache:

```sh
/usr/bin/time -l cargo test --offline --locked --release --jobs 1 \
  -p aspis-core --test r15_circle_domain -- \
  --exact r15_all_log20_fibres_are_canonical_circle_points --nocapture
```

Exit 0; one test passed, zero failed; test time 0.01 seconds; total wall
2.46 seconds; peak RSS 129302528 bytes; zero swaps. The small job's time was
predominantly compilation, not finite-field elimination. No full prover,
manifest replay, dependency download, or production-path change occurred.
Rustfmt subsequently changed formatting only. No Lean theorem changed;
`#print axioms` is not applicable to this executable test.

## Exact remaining boundary

This is exhaustive **finite executable evidence for the selected log-20
point routine**, not just a few fixture coordinates. It is not a kernel
proof of Rust semantics or of arithmetic on all QM31 operands. The generic
and exact-tower chord proofs already cover arbitrary qualifying OOD points;
this test supplies concrete evidence that all source query points satisfy
their circle-domain premise. The code/model correspondence of successful
OOD sampling and optimized inversion is still separate. No freshness,
reach, abort/retry/publication, or distinguishing-advantage bound follows
from this test alone.
