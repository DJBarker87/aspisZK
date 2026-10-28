# NDC stack-frame analysis handoff

Branch: `codex/cx-native-sbfstack-20261028`. Frozen source:
`4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Worktree starting revision:
`c777d9462bc90a7f008ccc5177c5adf2af50c0a6`. Local commits only; no push.

## Established claim and recommendation

[NDC_STACK_FINDING.md](NDC_STACK_FINDING.md) contains all **102 per-function/per-ELF
rows**, diagnostic offsets/estimated frames, runtime-source analysis and conclusion.
All **62 exact mangled instances across 34 function identities are absent** from
both complete linked symbol tables, associated by exact `.text` equality with the
three final stripped ELFs. No warned instance is on a TX1/TX2/Pool call path.
The three differently instantiated verifier `try_from_fn` functions are explicitly
separated and their direct stack accesses measured. The final relocation-aware
call graph has no unresolved direct calls; indirect calls are recorded as such.
This is not a complete indirect-pointer/alias/inline correctness proof.

Recommendation: **no source/build change or new P7 qualification for these34
warnings**, because their code instances are omitted. The reachable class(a),
class(b), class(c) sets are empty; do not recast omission as a fail-closed proof.
No class(b) target exists, so no conditional frozen-ELF VM test was performed.
No VM output/source-equivalence result is claimed.

All34 source families are also compiled in fresh native x86-64 client/prover
libraries. Native symbols establish31 non-generic/non-encoder identities;
two generic families have instance qualifications, and native LLVM/MIR establishes
the generic encoder. This is library membership, not final client-binary
reachability or privacy/stack safety. See native symbol, feature, emit and source
check JSONs. All391 selected native-source hashes match frozen Git bytes.

## Retained trust and precise remaining limits

No security/logical premise or trust row was discharged, added, widened or
reclassified. Compiler/linker P7, P6, SDK/std/runtime/ABI/persistence/syscall trust,
source/model association, security experiment transport, privacy and100-bit
PER-ATTEMPT soundness remain as before. S2/overall release target is not established
by this bounded artifact finding. No new theorem; `#print axioms`: N/A throughout.

The ELFs establish SBF V0, **not a validator release/feature configuration**.
Inspected offline SBPF0.21.1/Agave4.2.1 source explains both gapped and adjacent
frames: `virtual_address_space_adjustments` controls gaps; V0 execution admission
has separate flags. Gap-skipping accesses can reach other mapped frames: there is
no general current-frame bounds enforcement. The supplied receipts do not pin
which runtime/configuration a live validator uses. No RPC or chain observation ran.

Optional archive-authentication inspection NDC_I010 failed because the cached
SBPF directory lacks `.cargo-checksum.json`. Individual source bytes/hashes and
local package/VCS labels are recorded, but archive authenticity was not freshly
verified. The final scope was consumed; no extra launch or retry occurred.
A future unconditional deployed-runtime claim needs executable/source/build-feature
pins, the execution budget, active feature set, and authenticated runtime sources.
That limitation does not affect the omission result, which is runtime-independent.

## New versus reused evidence

Fresh: three ELF hashes; final and unstripped disassemblies/symbols and text
association; exact warning identity search; relocation-aware call graphs; frozen
source/IR call-shape cross-check; native optimized library build and focused core
MIR/LLVM emission; source hash check; runtime-source inspection; local evidence
validation. See [NDC_VALIDATION.json](NDC_VALIDATION.json) and
[NDC_validate.py](NDC_validate.py).

Reused: successful SBF reproductions NCR_B003 and NCY_B001/B002, their exact frozen
source/toolchain/features/build recipes and retained outputs. The full three hashes
were remeasured, with no changed artifacts. No full Lean manifest, Kani, SBF build,
field arithmetic gate, rank probe or prover execution ran. Coherent SInt2 objects,
Aeneas library and read-only leaf cache were not needed or touched; no Lean cache
was created, seeded or deleted. Only own native target files were removed after
pinning outputs; the named own cache was never deleted. No wallet/key operation.

## Attempts, resources and budget

**10/10 capped scopes used: 8 successful, 2 own-input inspection failures.
0 Kani, 0 Lean, 0 SBF VM runs.** No timeout, memory kill, raised cap, admission refusal
or unchanged failed resource-shape rerun. Every launch had exit0 AND allowed:true
admission. One scope at a time, MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64.
Native compilation was release/optimized, j2, offline/locked; heavy time was
compilation, not arithmetic. Cargo.lock hash remained unchanged.

NDC_I006 failed on an unavailable platform-tools `llvm-nm` path before inspection;
NDC_I007 repaired this own runner input by using `/usr/bin/nm`, keeping all checks.
NDC_I010's missing-checksum failure is retained, not credited as success. No shared
launcher, reservation tool, shim or workspace was repaired.

[NDC_ATTEMPTS.jsonl](NDC_ATTEMPTS.jsonl) records exact scope commands/targets,
exit statuses, actual task revisions, frozen source revision, script hashes,
dependency fingerprints, wall time, peak RSS, swap and axioms N/A. Full dependency
input records are in [NDC_INPUTS.json](NDC_INPUTS.json); exact GNU-time logs and
per-scope receipts accompany them. Wall time in the table is scoped GNU time;
transport-inclusive wall remains separately recorded in the ledger.

| Attempt | Exit | Scoped wall | Peak RSS KiB | Swaps |
|---|---:|---|---:|---:|
| NDC_I001 | 0 | 0:00.14 | 18220 | 0 |
| NDC_I002 | 0 | 0:00.86 | 84628 | 0 |
| NDC_I003 | 0 | 0:00.28 | 27728 | 0 |
| NDC_I004 | 0 | 0:00.08 | 19280 | 0 |
| NDC_B005 | 0 | 0:57.55 | 539520 | 0 |
| NDC_I006 | 1 | 0:00.07 | 30852 | 0 |
| NDC_I007 | 0 | 0:16.34 | 175740 | 0 |
| NDC_B008 | 0 | 0:20.44 | 560368 | 0 |
| NDC_I009 | 0 | 0:00.35 | 92704 | 0 |
| NDC_I010 | 1 | 0:00.14 | 56676 | 0 |

Only NDC_ files under this evidence directory were changed. Raw symbol/disassembly
transports retain their original hashes in compressed form. Transport-only empty
terminal lines and numbered-empty-line whitespace were normalized with original
hashes recorded in NDC_FORMATTING.json. Full reservation JSONs supplement the
launcher's compact admission stdout. No committed file exceeds20MiB.

Read-first shorthand paths were resolved to their immutable repository locations
under `docs/research/100bit-spend-path-20261013/` where needed (DIAGNOSIS and
S2LeadInterface). No session A live worktree or candidate was modified. Sparse
checkout remained enabled. No binaries, objects or keys committed.

Stage commits: `a4a97b7e1d` inventory; `a03c7f216f` analysis; `2dda24c240` handoff/receipts.
Final transport cleanup preserves NDC_I002 raw stdout/launch whitespace in `.log.xz`
with original SHA-256 sidecars and NDC_LOG_PINS.json; no measurement is changed. The next owner deliverable is to attach this bounded finding to
P7/S10 and retain the separate runtime configuration pin obligation. New scope
work requires a new budget; nothing is silently resubmitted.
