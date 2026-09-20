# R16 balanced transport: exact algebraic boundary

Date: 2026-09-20. Privacy source base `29eb3e83`.

`lean/AspisV8R16/BalancedTransport.lean` now proves, for any additive
commutative group, any finite inactive set containing the pivot, and any
permutation of row indices:

- Balancing the pivot by minus the sum of the other inactive entries gives
  inactive sum zero (`balance_sum_zero`).
- The transform sends that balanced vector to the permuted non-pivot
  entries and zero in the pivot coordinate (`transport_balance`).
- Every coefficient vector with zero pivot has an explicit balanced lift
  (`balanced_target_lift`). The lift changes only its input support and
  the pivot (`balance_preserves_zero`). Legality of that support is a
  separate source-inventory fact, not an implicit assumption of privacy.
- The implemented subtraction formula is a left and right inverse of the
  transform (`inverse_transport`, `transport_inverse`). The result is an
  explicit equivalence of message spaces (`transportEquiv`), not just a
  collection of basis tests.

This matches the mathematical shape of `tools/r16_basis_transport.rs`:
the final coordinate is the inactive sum, all other coordinates are copied
in the immutable order, and the inverse subtracts the other inactive
coordinates from that final value. The Lean function identifies the pivot
by `order j = pivot`; in the source the order fixes row 1023 at the final
position. The model does not pretend to extract Rust loops or field
operations. Source refinement must still establish the concrete permutation,
inventory support, field correspondence and circle-evaluator indexing.

In particular, `balanced_target_lift` does not assert a new distribution on
mask coins. Applying a deterministic correction to an existing mask and
proving its joint transcript distribution are separate obligations. The
equivalence above is on complete message space, not an assertion that every
message is a legal masked trace or that the protocol is sound.

## Focused compile evidence

All commands used cached `/Users/dominic/ZK/AspisFormal`, Lean 4.32.0,
`/usr/bin/time -l lake env lean -j1 -M1800`, explicit `-R` pointing to this
pack's `lean` directory, and output
`target/r16-lean/AspisV8R16/BalancedTransport.olean` in the privacy worktree.

| Changed leaf stage | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Balanced target lift | 0 | 8.10 | 1327775744 | 0 |
| Added inverse, wrong argument order in sum lemma | 1 | 8.40 | 1315848192 | 0 |
| Corrected inverse and injectivity | 0 | 9.05 | 1329332224 | 0 |
| Added right inverse and explicit equivalence, final | 0 | 6.47 | 1332035584 | 0 |

The failed compile's diagnostic `sorryAx` came from Lean's error recovery
and is not accepted evidence. The corrected final leaf has no errors or
warnings. Audits of the target lift, sum-zero theorem, left inverse,
injectivity and equivalence report only `propext`, `Classical.choice`,
`Quot.sound`. No runtime or unchanged full regression was repeated.

## First remaining proposition

Compose the concrete legal balanced lift and actual `T`/encoder with the
natural four-channel map at indices `4*k + lane`. The retained tests check
the concrete map and exhaustive domain factors, while the two new Lean
leaves prove its algebraic pieces; the complete source-refined composition
is still missing. Afterwards, raw coverage must be restricted to the
posterior of all earlier messages, not counted as independent fresh pads.
Full-transcript privacy, seed/shared-oracle refinement, soundness, and
failure/retry/publication accounting remain open.
