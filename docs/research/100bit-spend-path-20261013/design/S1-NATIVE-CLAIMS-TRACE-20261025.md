# Complete frozen Claims return and decoder trace

**New checked result:** the complete frozen native `claims` function, including
its actual fallible allocator and fixed three-row unsafe loop, satisfies the
return/decoder-call observations below under Kani's DEFAULT checks and an
explicit verified-decoder normal-return cut. All 747 checks pass and all three
covers are satisfied. **Initializedness is NOT checked by this result. S1 and
S6 remain OPEN; no enclosing SDK theorem premise is claimed removed.**

This addresses part of the former full-loop association gap, rather than
another lemma about a separately supplied owned row update. It does not claim
whole Rust memory safety, allocator TOTAL, native SDK installation, or closure
of the earlier initialization-check failures.

## Exact execution and observations

The harness calls the complete `claims` body copied literally from
`25866ec331cc7ce27dd9956609c11d32fa8fa58a:crates/aspis-r1-cost-probe/src/r1_semantic.rs`.
It retains the actual `Prefix.validated_record(25)`, actual frozen
`aspis_core::r0::heap::uninit`, real full private record/error/QM31/Box types,
three source pointer writes, early `?` returns, and final `Box::assume_init`.
No allocator, owned replacement, simplified error, arithmetic helper, or
candidate source function is substituted. Production files are unchanged.

Only `ValidatedRecord::decode_k` is stubbed. Its normal-return contract is an
overapproximation: each successful row has 29 independent full four-u32 QM31
values, including noncanonical values, and the first rejection may return any
of the eleven actual WireError variants with arbitrary variant fields. The
existing strict decoder/canonicality proofs are reusable child evidence, not
replayed or silently asserted as a native totality/abort proof here.

At every actual decoder call the stub asserts all of:

* exactly 29 output values; invocation index strictly below three;
* offset is 29 times that same invocation index;
* record row is 25, with the exact expected framed pointer and length;
* the next call counter is updated before returning that invocation's
  specified row or error.

The enclosing native function's observed return is checked without assuming
successful allocation, successful children or a desired output:

* If it returns an error without a decoder call, that error is Allocation.
* If it returns an error after a decoder call, the result is the exact selected
  first decoder error and the call count is its index plus one. No rejected
  suffix is called.
* If it returns a Box, all three calls occurred, no decoder rejected, and all
  348 raw u32 words in the actual three-row Box equal those same decoded rows.

The first-error, third-error and complete-success cases are covered. There
is no allocation-rejection cover, no allocation-law completeness assertion,
and no leak/complete destructor-effect theorem from this check. The default
allocator model's permitted outcomes and its eventual runtime binding remain
explicit limitations.

## Input/callee boundary and scope limits

The proof-only constructor returns the complete real private `Prefix`
carrier. Its root is zero and its 27 record references share a harness frame;
the native body accesses only record 25. That frame has zero backing bytes
and symbolic length from 0 through 3717 inclusive. Its contents are unread by
the overapproximated decoder; pointer/length identity is checked at the call.
This construction is not a proof of `Prefix::parse`, an arbitrary-prefix
representation theorem, or an SDK/account-domain transport. Applying the
result to arbitrary actual prefixes requires the projection/locality and
native caller binding; the concrete source's fixed record-25 access is
retained for that next join. The normally returned decoder cut also does not
cover a child panic, divergence, allocator abort or rejected transcript suffix
outside this function.

The three normally decoded rows are universal full raw words within that
harness domain, not honest fixtures or canonicality-restricted rows. No
`kani::assume` appears in the maintained proof. The default checks include
the required unwinding assertions at the retained bound32; this is not an
unbounded Rust execution proof. `--no-assertion-reach-checks` is the historical
harness setting, with the three named covers checked explicitly.

This does not retroactively validate initializedness. The separate
`s1-init-local-compile-v30` and `s1-init-step-v2` failures remain failures.
The union/niche limitations are why this distinct return/trace property uses
default checks; no default-check result is substituted for initialization
safety or R22 TOTAL. The isolated safe-storage source candidate remains
unadopted and is not used in this run.

## Before, after, and remaining joins

Before: a native ONE-row/default-check result plus an extracted owned-step
Lean induction supplied bounded three-row reference composition. The native
enclosing loop/return/early-error observations had not been checked together.
After: the complete frozen native function satisfies those observations in
the stated normal-return decoder/harness/Kani model. The older owned-step
and `three_rows_exact` results are unchanged and reused by reference; they
have not become an actual native whole-loop Lean theorem by this run.

Remaining for S1 include actual native allocation/initializedness/cleanup,
arbitrary-prefix/caller and native-to-extracted full-function association,
the concrete `FinishModel.Claims` installation, Terminal and remaining reached
mask/terminal domains, RustStd/arithmetic/abort/effects, and enclosing
source/event/oracle/release joins. The explicit base Ops and FinishModel B
in the already checked SDK source theorem are unchanged. No assumptions are
added to or removed from that theorem by this packet. S6's shared coherent
implementation/release join remains lead-owned. The <=2^-100 per-attempt
target, no-grinding requirement and two-transaction format remain unchanged
and **not yet established**.

## Validation and provenance

| Target | Exit | Wall s | time RSS bytes | Observed aggregate RSS bytes | Swaps |
|---|---:|---:|---:|---:|---:|
| `s1-native-claims-v1`, smallest compile only | 0 | 0.683688 | 223461376 | 193036288 | 0 |
| `s1-native-claims-v2`, full-function return/trace | 0 | 20.196097 | 1024655360 | 1077477376 | 0 |

Solver-reported verification time is 19.431238s. Both jobs used the shared
atomic local compiler lock, one Cargo job, warm cache, 2 GiB aggregate-RSS/
64-process/180-second watchdog; no stop fired and no unknown lock was removed.
Short-job aggregate sampling is reported separately from time's maximum RSS.
No NUC/SSH, extraction, Lean theorem compilation, SBF build, source adoption,
runtime or unchanged package replay occurred.

Same pinned official Kani0.67 Mac asset/Rust commit `53732d5e0` as the prior
diagnostics. Every Kani package file, Rust/Cargo, top-level host dylib and
target sysroot library file is pinned before and after, along with all source,
manifest, lock, command, environment and raw logs. System OS/runtime frameworks
and compiler correctness are not thereby certified. This is macOS/aarch64
model-check evidence, not Linux/SBF identity. `#print axioms`: N/A, no Lean
declaration or custom axiom was added.

Source-only `focused-extractor-proof-packet-v1` evidence is under
`evidence/s126-current-caller-20261021/s1-native-claims-20261025`,
`s1-native-claims-v1` and `s1-native-claims-v2`. The old source/tool packets
and existing parser/owned-step Lean evidence are reused without replay.
The read-only scope/hash check passes:

```
python3 tools/s1-native-claims-20261025/check.py
```

Pinned original source/raw log whitespace is preserved; maintained proof,
tools and report are checked separately. No binary enters Git.
