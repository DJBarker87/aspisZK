# NFZ source resolution and blocked compiler review

**Incomplete. Neither inventory repair is admitted.** Frozen Rust is
`4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`; baseline is the pinned NFX ledger.
All source reads come from immutable Git objects, recovered in
`NFZ_FROZEN_SOURCE.json.xz` with file pins in `NFZ_SOURCE_PINS.json`.
No session A worktree was accessed.

## TX2:046 — type, trait member, callers

`field/wide_exact.rs:29` defines the `WideExact` type and its inherent methods.
It contains **no inherent `WideExact::from_m31`**. `r0/scalar.rs:3` imports that
same type; lines 87–91 implement `CodeField` for it. The inventory function is
`r0/scalar.rs::WideExact::from_m31`, body SHA256
`b36ae7be0a9543995f8f2fc48ac1f0621481162aae8f52f98ff5c535ab5dae8c`.
There are not two functions named `WideExact::from_m31` in these two files.
The inherent `WideExact::from_qm31` is a distinct function.

The frozen source has four `CodeField` impls: M31, CM31, QM31, WideExact
(scalar.rs lines 41, 56, 70, 87). The embedding chain is:
WideExact trait embedding → QM31 trait embedding → CM31 trait embedding →
M31 trait embedding; the return construction also invokes inherent
QM31::from_cm31, CM31::from_m31 and WideExact::from_qm31. Inherent-method
precedence matters: the CM31 constructor in scalar.rs:59 is the inherent
field.rs method, not recursive trait dispatch.

Within the 434 unique inventoried function bodies, the AST and independent
lexical pass agree on all 26 `from_m31` sites:

- Transcript<H>::queries, transcript.rs:56–77: 22 calls through alias E,
  imported as WideExact. H is a digest parameter, not the field parameter.
- accumulate_batched_with_node, verifier.rs:285: E is the same concrete
  WideExact alias. This caller is in slice Q.
- scalar.rs:90: explicit `<QM31 as CodeField>::from_m31`.
- The two statement `lift_m31` helpers use the inherent CM31 constructor.

These are source-resolution observations, **not a compiler-backed TX2
reachability result**. Source outside the inventory also includes
accumulate_with_node:263, generic domain.rs::fibre_point<E>:72–73 and
basis.rs::Re3Plan::apply<E>:215. Their monomorphised entry reachability has not
been certified. The no-op release trace body does not justify deleting an
argument-evaluation edge without compiler evidence. TX2:046 is retained OPEN;
it is not marked REACHABILITY-EXCLUDED.

## TX2:211 — callback sites

`lib.rs::first_decoded`, line 50, passes the bare function item `error` to
`Result::map_err`; `error` at line 40 logs the verifier error and returns
InvalidInstructionData. The frozen source has one other `.map_err(error)`:
line 79 inside the `not(feature="pool-adapter")` legacy entry block. That
block is source-cfg disabled for the selected deployed features. A deployed
MIR dump must corroborate the distinction. No other named error callback site
was discovered in the inventoried bodies. Rejection-path call semantics,
ordered logging and execution reachability remain unproved by this job.

## Whole-inventory discovery and limits

`NFZ_scan.py` scans all 587 occurrences / 434 unique bodies, plus every
CodeField embedding implementation. It uses tree-sitter 0.25.2 and
 tree-sitter-rust 0.24.2, matching the original inventory parser pins.
`NFZ_CANDIDATES.json` records 39 unresolved candidate edges, including unknown
target identities, overload/cfg qualifications, and existing-row membership.
This is a discovery overapproximation, not an exhaustive compiler resolver.
`NFZ_SCAN.json` retains all 239 relevant sites, including anonymous closures
whose calls belong to their enclosing function.

Additional source candidates include `input.map(extension_limbs)` in
state_only_poseidon.rs:218 (existing row), and the fallback closure in
sampler.rs:122–126 (circle_fallback_point has no existing inventory row).
The three scalar trait embeddings M31/CM31/QM31 also have no existing rows.
These four potential new functions are reported explicitly; no new rows are
silently omitted from an admitted repaired graph. Recursive discovery from
new nodes and monomorphised classification still need compiler authority.

## Compiler attempt, own validation defect, and independent check

NFZ_B001 obtained reservation `allowed:true` with exit 0, and entered exactly
one scope with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64.
It failed **before cargo check or diagnostic rustc ran**, in my own metadata
validator: I required every package in Cargo.lock to appear in metadata.
Cargo omitted exactly the three disabled optional local packages already
permitted by NFQ: aspis-z4b-probe, aspis-r1-cert-check, aspis-r1-cert-build.
There were no added package identities or mismatched dependency edges.
This is an own-script error, not dependency drift or an infrastructure fault.

The original source and failure are preserved in NFZ_B001/. The corrected
NFZ_check.py uses the frozen optional-package projection and additionally
checks that r1p-check is absent and the optional dependency remains optional.
`NFZ_PREFLIGHT_DIAGNOSIS.json` checks the retained metadata without compilation.
The corrected script was **not rerun**: the job's explicit ONE-scope limit is
preserved. No timeout, memory kill, cap increase, Kani, extraction, Lean,
Rust type-check build, or ELF rebuild occurred. The frozen lock remained
5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef.

Exact rustc/cargo versions and runner hash are in NFZ_TOOLS_AND_LOCK.json:
nightly-2026-09-17, rustc 1.100.0-nightly commit 923c95cdf5ba65cea505aa2ea829f578e1506ed8;
cargo commit 495c385d0875c4ba51eb72ea0448a2d4c018b8d4. Read-only version
queries are not compiler proof attempts. No target directory or MIR file was
created. Retained extraction workspaces inspected read-only exposed LLBC,
not the requested independent deployed MIR authority; no credit was inferred.

NFZ_INDEPENDENT_CHECK.json compares a second lexical enumeration with the AST
and agrees on the 26 embedding sites and both named error callback sites.
**It does not meet the requested second MIR/symbol-level check.** Consequently
NFZ_EDGES.json is empty and NFZ_OVERLAY.json is explicitly blocked. No reviewed
edge, native bridge, reachability exclusion or security premise is claimed.
