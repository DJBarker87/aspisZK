# V7 production normalized-fold canonicality

Source parent: `09b1d8c90`. Focused Lean 4.32.0 checks on
`dombarker@100.108.41.90` reused the compiled cache and invoked
`check-r30-decoder-focused.sh` (`lake env lean -j1 -R`) inside independent scopes
with `MemoryHigh=7G`, `MemoryMax=8G`, `MemorySwapMax=0`.

| Target | SHA-256 | Scope | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | --- | --- | --- | --- | --- |
| `V7ProductionCallbacksR30ArrayCanonical.lean` | `cdfc879dadf5a56145c8d88bf54ed3f4bdd482a85c28579a61f4d51d735eb78d` | `run-r0e280ad7d0cb4c8da4390ef10caed7b4.scope` | 0 | 1.81 | 2,679,648 | 0 |
| `V7ProductionCallbacksR30NormalizedFoldCanonical.lean` | `4b017ab76155d4e71519c58862c36f4ec564e4b6d921157c8e096b9f57a8b000` | `run-r4034530065db4c2da0ea4e985addb8bb.scope` | 0 | 1.78 | 2,686,668 | 0 |

`array_index_all` audits to `[propext, Quot.sound]`; `array_update_all`,
`successful_normalized_candidate_canonical`, and
`successful_normalized_polynomial_refs_canonical` audit to exactly
`[propext, Classical.choice, Quot.sound]`.

The source fold theorem assumes canonical input QM31 values and a successful
literal polynomial call. It follows the returned source intermediates:
the constant coefficient is canonical by checked additions and halves, and
the three-product contribution is canonical by channel reduction before the
final addition. All source computations remain in the execution equation;
no concrete recurrence or packed limb array is normalized.

This theorem asserts successful-output canonicality, not polynomial equality or
overflow-free semantics. Query-array/callback lifting and the terminal
`runningCanonical` premise remain outstanding. No full manifest was run.
