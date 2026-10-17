# C2 known-host construction checkpoint

**HISTORICAL_CONTEXT_ONLY — 17 Oct cache audit.** These archived semantic-model
results are excluded from current accepted results. Both targets import the
old `FS2.Duplex` (`fd269bd4…`) and `UniformStateFirstHit` (`b0d7a107…`) objects.
The resolved Circle object is the repaired `05c7d259…`, not rejected `39ea3fa6…`.
The exact source import paths, selected object hashes and repaired comparisons
are in `../c2-historical-context-20261017/audit.json`. All original receipts and
archives remain unchanged. Current actual embedding and six freshly checked
construction-core lemmas are isolated from these historical model imports in
`../c2-host-embedding-20261017/`. No whole semantic-model replay was attempted.

The conditional construction component is checked. The actual `Backend::c2`
and `Commitment::build` source bridges remain **open**: both exact roots have
valid Charon LLBC and fail Aeneas. No actual C2 custody result is claimed.

`C2OwnedHostConstruction.lean` starts with supplied owned H1/G rows, applies
explicit embedding/variant transport/project/check/encoder operations in C2
lane order, and constructs an owner from the successful encoder returns. Its
inversion theorems derive retained rows and the two encoder outcomes from the
model's successful execution. The literal word indexes those retained vectors;
actual vector lengths and raw-field interpretation remain explicit. The
semantic callback selects those same entries. There is no zero C2, root-based
recovery, sampler substitution, or premise asserting the desired final word.

This is a conditional functional model, **not** the extracted Rust body.
`source-model-map.json` identifies every executable definition/boundary and
omission. In particular it does not establish Backend error-state mutation,
full constructor allocation behavior, actual encoder correspondence, supplied
H1/G production, bytes/root binding, or complete semantic transcript execution.
Packing/salt-path/custody/checkpoint authentication remain separate.

## Focused result

| Target | Attempt | Exit | Wall | Peak RSS KiB | Swap | Axioms |
|---|---|---:|---:|---:|---:|---|
| `C2OwnedHostConstruction` | construction-f | 0 | 2.300 s | 3,531,060 | 0 | 9 reports: 6 `[propext]`, 3 `[propext, Classical.choice, Quot.sound]` |

Source base `deb68369ba3ad7cc6706dc24b6503fac1cbe942b`; exact changed Lean source
SHA `952479754bae430642a69fde3f6ef8f6598b23d066a243999a9a752d1a7d79c4`.
The input was checked through `lake --no-cache env ... lean -j1` using pinned
4.32.0 imports, without rebuilding dependencies. Scope: MemoryHigh6GiB,
MemoryMax8GiB, MemorySwapMax0. Atomic prelaunch external-Lean check plus a200ms
monitor found no overlap. Prior failed source/logs are retained. Attempt d was
suppressed before launching Lean when external PID3462473 appeared; its guard
record reports no formal-result metrics. No external process was signaled.
The historical successful runner records the cgroup cap but not an aggregate
reservation snapshot; the parent granted this sole Lean window while C paused.
Extraction receipts do include aggregate populated cgroup reservations.

## Actual-source extraction and retained diagnostics

| Exact root/input | Charon exit / wall / RSS KiB | Aeneas exit / wall / RSS KiB | Status |
|---|---|---|---|
| actual caller | 0 / .403 s / 185492 | 2 / .603 s / 72512 | `SymbolicToPureAbs.ml:1313`, whole c2 span |
| actual constructor | 0 / .406 s / 197172 | 2 / .604 s / 94512 | `InterpJoin.ml:2209`, borrowed C1/C2 index-slice match |
| hash-carrier diagnostic | 0 / .403 s / 184664 | 2 / .402 s / 71984 | Replacing hash carrier does not fix caller |
| indexed two-copy diagnostic | 0 / .202 s / 171072 | 2 / .402 s / 66176 | duplicate columns borrow projector |
| destructured two-copy diagnostic | 0 / .402 s / 170192 | 2 / .402 s / 66000 | same duplicate projector |

Every extraction receipt records exact command, tool/source pins, exit, wall,
RSS, swap0, caps and reservation. These are compiler attempts, not formal
results; `#print axioms` is not applicable. No generated caller/build Lean is
accepted. Diagnostics are explicitly `REJECTED_DIAGNOSTIC`; no production file
was changed. The constructor cut's opaque encoder signature weakens CodeField
to Copy solely for typechecking, explicitly recorded in its pins. That input
is not an accepted source-refinement theorem or an encoder implementation.
PrivateSalts destruction/volatile erasure is outside the cut.

## Re-pins and reproducibility

`source-inventory.json` repeats the accepted design's negative Rust inventory:
440files, zero `C2Word`/`literalMessage` identifiers,42 exact declarations. At
deb all42 declaration hashes match the old3da design except the expected tx1
refactor. `source-repin.json` and `source-model-map.json` pin47 selected Rust
slices at the final A1d/e/qualified1f source
`1b98d3cf35fb1959da75bcec0a396f182d4b1f3d`; all are byte-identical to the deb
extraction inputs. This is source equality, not an executable refinement proof.
The full known-host chain still requires mapping the actual successful owner
execution, actual encoder vector lengths/content/interpretation, and H1/G
production into the conditional construction.

`checkpoint.tar.gz` SHA
`4cb40c08ae1c2238cedb5013a3ae404d77c69387e578270f78ff243739c2c112`
retains296 exact files: all original/diagnostic inputs, valid LLBCs, compiler
receipts/logs, every failed/suppressed Lean input and successful object/log.
`checkpoint-members.json` hashes every member. Run the kit's
`check-evidence.py` for read/hash verification. `prepare.py --check`,
`prepare-build.py --check`, and `source-model-map.py --check` are deterministic
read/hash checks. No SBF, runtime harness, native arithmetic gate, full replay,
live-worktree or module change was performed for this checkpoint.
