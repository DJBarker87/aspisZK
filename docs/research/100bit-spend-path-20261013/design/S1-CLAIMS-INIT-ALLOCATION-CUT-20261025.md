# Claims initialization diagnostic: allocation-independent union obstruction

S1/S6 remain OPEN. No initialization proof or enclosing premise removal is
claimed. This changes the next action: changing the allocation setup alone
cannot make the frozen Claims loop pass the retained Kani initialization
checker. Do not retry these runs unchanged or increase their caps.

## Exact source and experiment

The complete frozen private `claims` body is unchanged from
`25866ec331cc7ce27dd9956609c11d32fa8fa58a`, including the native
`Box<MaybeUninit<[[QM31;29];3]>>`, raw row writes, `?` operators, and final
`assume_init`. The full frozen wire module, native Error and QM31 carriers are
retained, with only the existing proof-only Prefix constructor appended.
There is no simplified error or returned carrier.

Two explicit child cuts are used:

1. `heap::uninit<T>` returns a Box over fresh RAW UNINITIALIZED allocation from
   `alloc::alloc::alloc(Layout::new::<T>())`. It does not zero storage or supply
   an initialized Claims value. Allocation success is part of this diagnostic
   setup; actual fallible Vec allocation, rejection, cleanup and runtime
   association are NOT proved by it.
2. `ValidatedRecord::decode_k` checks the same row-25 token, pointer, length,
   N=29 and offsets 0/29/58 before returning symbolic full raw QM31 rows.

v1/v2 initially include all normal decoder-error prefixes. Verification fails
on Kani's unsupported initialization layout for the real WireError enum:
variants have different padding. v3/v4 fix decoder success but still construct
and move that Error value in the proof harness; the same layout failure remains.
v5/v6 remove those unused Error values and branches FROM THE HARNESS, while
retaining the full native Error and unchanged Claims function. This is an
accepted-path initialization diagnostic, NOT replacement coverage for arbitrary
rejections. It reaches the actual native `out.as_mut_ptr()` at line 11 and
fails: “Interaction between raw pointers and unions is not yet supported.”
All actual row words remain symbolic and every returned word is compared.
No `kani::assume`, transmute, source/compiler patch, initialized-storage
substitution or disabled initialization check is used.

## Why the proposed pointer-cast workaround was not run

Read the primary Rust source at the actual rustc commit prefix `53732d5e0`,
`library/core/src/mem/maybe_uninit.rs`. Its `as_mut_ptr` ALREADY uses
`self as *mut _ as *mut T`, with a comment explaining the transparent
representations. Thus replacing it by the proposed direct cast is not a
materially different operation and gives no defensible new retry.

`tools/s1-claims-init-allocation-cut-20261025/rust-source-origin.json` records
the exact primary URL and full downloaded file SHA256; the selected method
excerpt is retained. The web fetch first returned a cache miss; a bounded
read-only direct fetch succeeded. This is source inspection, not source/binary
identity: installed compiler/sysroot binaries are separately pre/post pinned,
and no reproduced std build is claimed. No pointer-reference equivalence
harness or initialization proof was run or accepted from this observation.

## Exact validation

Target in all runs:
`native_claims::proofs::native_claims_init_allocation_cut`.
Kani 0.67.0 official Apple Silicon distribution and rustc
`1.93.0-nightly (53732d5e0 2025-11-20)`, same package/archive provenance as
`S1-NATIVE-PREPARED-CONTROL-20261025.md`. Each input pins full package/compiler/
host-sysroot files and all 88 core source files before/after. Source-only
snapshots and exact commands/logs are retained. `-Z uninit-checks`, unwind 32,
unwinding assertions and default overflow checks remain enabled. Rust is
optimized; no resource-option overrides or custom axioms. `#print axioms` N/A.

| Attempt | Scope/result | Exit | Wall seconds | Peak RSS bytes | Sampled aggregate bytes | Swaps |
|---|---|---:|---:|---:|---:|---:|
| v1 | all-normal-error-prefix compile | 0 | 2.515528 | 358825984 | 301121536 | 0 |
| v2 | Error padding unsupported, 1/606 failed, 0/3 covers | 1 | 1.363307 | 119422976 | 90243072 | 0 |
| v3 | fixed-success compile with unused Error setup | 0 | 2.510590 | 339247104 | 281542656 | 0 |
| v4 | Error padding unsupported, 1/602 failed, 0/1 covers | 1 | 1.891283 | 116260864 | 87162880 | 0 |
| v5 | accepted-path compile, no unused Error setup | 0 | 2.044792 | 318095360 | 265256960 | 0 |
| v6 | frozen union operation unsupported, 1/469 failed, 0/1 covers | 1 | 1.356856 | 130138112 | 100401152 | 0 |

All jobs used the shared atomic local compiler lock, sampled aggregate 2 GiB
watchdog, 64-process bound, 180-second timeout. No watchdog fired. This is
ordinary focused Mac execution, not hard cgroup/no-swap isolation; process
swap observations are zero. No SSH, NUC, heavy build, full replay or cap rise.
Nonfailing checks and code generation are NOT accepted partial proof credit.

An evidence collector check exposed a snapshot-path bug in this new runner:
all six runs pre/post HASHED the correct selected root
`min/src/probe_claims_init_cut.rs`, but the snapshot copied the unused prior
`probe_prepared.rs`. The unused file is checked against its historical source
and explicitly excluded as an execution pin. Maintained `probe.rs` reconstructs
the correct contemporaneous selected-root hashes. This is not retroactively
called a snapshot. First audit failure is retained; the future runner path is
corrected without compiler rerun. All selected native bodies and proof harnesses
have their contemporaneous snapshots and hashes. Historical raw receipts are
unchanged. A passing failure audit establishes none of the failed properties.

```
python3 tools/s1-claims-init-allocation-cut-20261025/check.py
```

The source-only focused-extractor-proof-packet-v1 audit passes 93 file hashes,
exact frozen Claims body, unchanged wire carrier, all six receipts, child cuts,
compiler/tool/source stability and the excluded failures. No binaries shipped.

## Remaining obligation and next route

The prior normal-return native Claims trace (`c6107eb726`) and accepted SDK
Claims ranges (`cef39d839d`) remain valid at their published scopes. This
failed initialization campaign does not withdraw those or establish memory
initialization. The safe-storage source candidate `891a213f79` remains NOT
ADOPTED, and its source-only extractor kit remains unexecuted pending separate
fresh build-host admission. That candidate still needs its allocation/error/
effect equivalence, extraction, caller, cost and re-pin gates; a status label
cannot discharge them.

The frozen native initialization gate now requires a supported semantics/tool
route through union-pointer AND allocator/Error layout handling, or a fully
validated equivalent source route. Merely changing Box setup, fixing decoder
success, repeating the direct cast, disabling checks or raising memory does
not close it. Coherent source/caller/runtime/SDK/hash/oracle/release-artifact
joins remain separately open. No production-source decision, adoption, security
contract change or <=2^-100 conclusion is claimed here.
