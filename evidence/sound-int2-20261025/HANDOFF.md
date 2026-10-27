# SInt2: checked D189 / selected Claims composition

S2 OPEN; target not yet established. Branch `codex/cx-sound-int2-20261025`.

## Established statement

`lean/SInt2_AcceptedPairClaims.lean`, theorem
`AspisR1.ClaimsUnrolledSdk.accepted_pair_claims`, now compiles. Its source is
byte-identical to retained attempt30 except the import of
`SInt2_ClaimsUnrolledSdk`. In particular, its quantifiers, hypotheses and
conclusions are unchanged. `SourceCuts` is an output derived by D189;
no caller output, independently selected cut, or second existential execution
is added as a hypothesis.

The proof first destructures `S2W_D189Consolidation.accepted_run` into its
actual `f,s,outer,pre,middle,fs,ss`. It passes THAT `f,s` and THAT derived
`cuts` to the canonical-owner SDK consumer. The result exports:

- the same source cuts, expanded run, owned run and projected schedule;
- the same account observations and unchanged second heap;
- the selected semantic public/cut, wide view, successful semantic call,
  parsed Claims prefix and normalized Claims from that same call;
- D189's conditional Required14 and reached-site equivalence for that pair.

This closes the retained duplicate-owner / unchecked same-witness composition
row. It does not instantiate a frozen2 AcceptedRunJoin or headline interpreter.

## Canonical owners and workspace

One workspace was created:
`/home/dombarker/project-offloads/codex-cx-sound-int2-20261025`.
It uses unchanged copies of the existing `S2W_lean_host.py` and
`S2W_run_host.py`; no launcher, monitor, admission or metadata tool was written.
`object-source-manifest.json` records the pinned cache selection and source
provenance. `final-closure-manifest.json` records the actually selected target
closure, including object/sidecar hashes and new source hashes.

`SInt2_SdkDependencyFactorV1` imports D189, replacing the copied bytesOf,
account, entry, wrapper, observation and extraction declarations.
`SInt2_S6SdkSourceCutTypesV1` also imports the canonical FirstCut/SecondCut/
SourceCuts owners rather than duplicating them. The originalFirst bridge now
abbreviates the canonical complete wrapper and proves its equality directly.
The other affected consumers change import names only. The final import graph
excludes both old copied-owner modules.

The reused session A candidates come from immutable git revision
`d346dc7cb7232f12c4ff930d1e2db320bdc101d9`; their live worktree was not read or
written. 404 selected candidate objects match both original acceptance-receipt
source hashes and object hashes. This includes all four named S1/S6 prerequisite
roots. ClaimsUnrolledVerify's source matches retained receipt26 and its object
is pinned by the retained SDK manifest. All 57 canonical host sources with corresponding repository modules match
exactly, including the D189 chain (`canonical-source-check.json`). Historical
package/core and unchanged canonical caches were reused; this is a focused composed proof on that pinned
selection, not a fresh full frozen-release rebuild. The manifest explicitly
records the 76 historical D189/SDK object-hash variants rather than treating
their binary hashes as equal.

## Validation and budget

All 15 Lean attempts passed: BUILD-SInt2-001 through 014, then SInt2-001.
Each used `lake env lean -j1 -M7000 -DElab.async=false` in its own systemd scope
with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. No cap increase,
timeout, memory kill or unchanged compile rerun occurred. The existing runner
verified the cgroup limits. The host preflight had no other populated build
scope; this job used one 8 GiB reservation at a time.

SInt2-001: target `SInt2_AcceptedPairClaims.lean`, exit 0,
wall 2.271117519 s, peak RSS 5,252,624 KiB, swap 0; source revision 4fc79abab0 with the
new source tree dirty, exact source hash recorded in the receipt.
`#print axioms accepted_pair_claims`:
`[propext, Classical.choice, Quot.sound]`.
All new top theorems have full printed audits in their receipts/stdout;
only those three standard axioms occur, or none. Per-attempt receipts record
exact command,target,source revision/hash,direct dependency hashes,exit,wall,
peakRSS,swap,cgroup and axioms. Source snapshots are the committed SInt2 files;
no objects/binaries/ELFs/tarballs are committed.

Budget used: **15/150 Lean (14 dependency builds + 1 proof), 0/20 Kani**.
No Rust, Kani, SBF or full frozen-manifest replay was run: no covered shipped
source/artifact changed and no release result is claimed. Static source checks
found no sorry, axiom, admit, native_decide, heartbeat/depth overrides or absolute
machine-specific paths in the new modules. `git diff --check` passes.

## Assumptions and next blocking row

No cryptographic/security hypothesis, trust item, carrier, failure event or
security metric is changed. No existing runtime/native implementation premise
is discharged. The SAME pair now composes; the former ownership/import
obstruction is removed.

Retained: S2TrustedSdkBorrow's adopted library contract, TrustedStd copy,
allocator/runtime entry admissions, both accepted native wrappers, the exact
candidate installation's AeneasExtraction stage1/stage2/digestSource boundary,
P1/runtime syscall, expanded child port/marks, writer/reader cone joins,
cross-transaction CheckpointVersionBinding,P2Prime and the listed first-entry/
multiproof/S8 child joins. Claims reserve/intoBox operations and native
mapError/boxArray, ownership, cleanup, ordered effects, source equivalence,
adoption and artifact correspondence remain uninstantiated. This result does
not convert an implementation-refinement gap into a cryptographic assumption.

The next open body in TX1 call order is **shape/op3**, followed by **scan/op4**:
prove their concrete source/ROM laws on this exact installed dictionary and
accepted execution. Then batch/op5 still needs full Result/effects/carrier
interpretation and indexed authentication of the Q1 selected map. The later
Q1/Q2/Claims installation compatibility, op18 same-saved-checkpoint state,
op19 FinishOps, raw canonical frozen2 join, rejected oracle prefixes and
runtime/query-budget/source-to-ELF obligations remain as documented in
`design/SOUND-INT-20261025.md`. This task supplies the previously missing
checked D189/S6/S1/Claims same-witness predecessor, not those later rows.

No shipped file or cfg(kani) harness changed, so the ELF rebuild trigger did
not fire. Inherited pins, not newly reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

All stage commits remain local; no push. The 100-bit release target remains
not established.
