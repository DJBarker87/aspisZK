# Gamma reuse: complete transaction caller composition

`CuSavingsGammaTx1.source_eq_of_claim_factor` now proves equality of the complete
actual old/new `tx1` functions at candidate 1, consuming the previously checked
full preparation bodies and retained-table invariant. The new `tx1_prepare` and
`tx1` source bodies are byte-identical to production
`39c2971dd16c95858a4cfd2c9ae35da052eacfa9`. No production Rust changed.

This closes the transaction-wrapper composition left open at `1ab6ef4ae`,
**conditional on the explicit local claim-factor equation**. That equation still
needs source discharge. This is not candidate or full-goal completion.

## Actual source, not newly assumed preparation behavior

`extract-gamma-callers.py` extends the exact pinned gamma extraction kit with
both complete tx1_prepare/tx1 bodies from candidate
`3ab4faf7f5b488a0c82720717656a0ebf4c46efa` and its parent. It retains exact source
fragments and records the source spans, hashes and layout adjustments. The only
caller-body adaptation is renaming `Prepared::new` calls to the paired inherent
method names that already hold the exact complete preparation bodies.

`verifier.mark` has its unchanged complete body. Semantic verification,
View.parse, Accumulator.new and tx1_finish are shared explicit source boundaries.
The unchanged finish body is archived on both candidate sides. Its later
optimizations are separate candidates: this theorem is universal in the shared
finish interpretation and does not silently prove those changes.

The original pinned frontend emits all complete caller bodies with `-checks`
and `-abort-on-error`, without compiler changes or LLBC normalization. The two
preparations are opaque only in this **caller emission**, then bind directly to
`AspisR1CuGamma.Funs`' actual previously checked preparation definitions.
`CallerBoundaries` has exactly four shared helper fields and no preparation or
powers fields. No generated axiom template is imported.

`emit-gamma-callers.py --check` compares shared carrier/constant declaration
bodies exactly before reusing them. It removes thirteen identical type
declarations and two identical constants from the promoted emission and imports
the original checked ones. Every remaining generated caller/helper body is
unchanged. This prevents duplicate nominal carriers while making the source
preparation theorem applicable without a new conversion premise.

## What the theorem covers

The statement quantifies over public input bytes, proof bytes, k, hash, arbitrary
observer callbacks and arbitrary shared helper results. It preserves:

- k > 22 rejection and parsing failures/divergence;
- semantic verification, semantic-error mapping and both early observer calls;
- preparation errors/divergence and the exact semantic-claims handoff;
- accumulator allocation before consumption of the reused power table;
- the Prepare observer and actual finish call with the same table and arguments.

No parser-success, semantic-success, observer-termination or allocation-success
hypothesis is supplied. The retained table equality comes from successful
**actual** new preparation. Deleting the duplicate call is justified even when
other operations fail before table consumption.

The only changed-helper premise is, for arbitrary sem/v/gamma/kappa:

```
oldClaim(D, sem, v.y1, v.inactive, gamma, kappa)
  = do g <- powers(29, gamma); newClaim(D, sem, v.y1, v.inactive, g, kappa)
```

The theorem proves equality in the original compiler Result model. A pure
result equation is not, by itself, the final full ordered-oracle/public/effect
observation theorem. That composition, all remaining candidate contracts and
application of the original soundness/privacy results remain required.
Original Box/SDK/runtime and shared helper source boundaries remain explicit.

## Focused evidence and current NUC policy

The latest user instruction was: **“status update. no nuc limits”**. It supersedes
the earlier NUC resource/concurrency caps. New plans explicitly record this
instruction. NUC scopes now have memory.high/max/swap.max all `max`, no TasksMax
cap, no Lean `-M` cap and no wrapper timeout. Foreign Lean activity and actual
resource usage remain recorded; host-idle admission and aggregate reservation
caps are removed in this explicit mode. Same-module output writes are locked
to prevent corrupt cache artifacts. This is not a host resource/concurrency cap.
The old capped mode remains available for historical plan compatibility.

Focused-first proof cadence, source/cache pin checks, command/revision/features,
exit/wall/RSS/swap receipts and `#print axioms` checks remain in effect. No broad
or unchanged successful replay was run to suppress an unused simp warning.

| Target | Receipt | Wall seconds | Peak RSS KiB |
|---|---|---:|---:|
| AspisR1CuGammaCall/Types | cu-gamma-call-types-a | 2.005 | 2,624,720 |
| AspisR1CuGammaCall/FunsExternal | cu-gamma-call-externals-a | 1.604 | 2,598,044 |
| AspisR1CuGammaCall/Funs | cu-gamma-call-funs-a | 1.804 | 2,629,728 |
| CuSavingsGammaTx1 | cu-gamma-tx1-a | 1.804 | 2,613,332 |

All four successful Lean targets print only standard Lean axioms and observed
zero process/cgroup swap. The Charon preflight initially failed on a missing
`Phase` import (cu-gamma-caller-charon-a, exit 101); its exact input/source pins
are retained. Adding that layout import gives cu-gamma-caller-charon-b, exit 0,
0.401 seconds, 205,168 KiB RSS. Strict caller emission then passes in
cu-gamma-caller-aeneas-a, exit 0, 0.802 seconds, 90,992 KiB RSS. Neither required
a compiler change. No ELF, shared object, object/cache binary or wallet key was
committed or removed.

## Re-pin inventory

These are the exact additional extracted caller declarations corresponding to
this already-retained production change; no additional production function was
edited in this checkpoint.

| Rust function | Extracted Lean declarations consumed/re-pinned |
|---|---|
| tx1_prepare | AspisR1CuGamma.gamma_old.tx1_prepare; AspisR1CuGamma.gamma_new.tx1_prepare; their Semantic error-map closure call_once/FnOnce declarations |
| tx1 | AspisR1CuGamma.gamma_old.tx1; AspisR1CuGamma.gamma_new.tx1 |
| mark (unchanged) | AspisR1CuGamma.verifier.mark |
| Prepared::new | Existing AspisR1CuGamma.gamma_old.Prepared.gamma_old_new and gamma_new.Prepared.gamma_new_new imported directly |
| Public/Accumulator/Phase carriers | AspisR1CuGammaCall.Types; thirteen other source-identical carriers reused from AspisR1CuGamma.Types |

The preceding goal turn made progress by pushing the gamma preparation/dataflow
checkpoint. This turn adds the consuming complete source tx1 theorem. The full
equivalence/security goal remains active, with the claim source bridge next.
