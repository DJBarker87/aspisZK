# ARR account rejoin3 handoff

**Target not yet established.** Branch codex/cx-account-rejoin3-20261026.
Start b8c6f579ef953f3e55a80489124df80701172d02. No push or merge.

## Actual-top before/after and ledger

Actual latest target remains `AspisR1.Rc10_Top.deployed`. BEFORE and AFTER are
literally identical: ARR_BEFORE_SOURCE.lean.txt and ARR_AFTER_SOURCE.lean.txt.
ARR_BEFORE_KERNEL.lean.txt and ARR_AFTER_KERNEL.lean.txt are identical copies
of the inherited fresh Rc10 kernel print, with provenance explicitly recorded
in ARR_KERNEL_PROVENANCE.json. They are NOT fresh ARR root prints.
The unchanged root could not be loaded here because historical imported objects
were missing. No ARR_Top.deployed or replacement root is installed.

ARR_LEDGER_DELTA.json mechanically recounts the SAME original atomic rows,
scopes, native/global families and alias L185 -> L159; no packaging discount.
Before=after: actual83T/12P/13G/0C; distinct non-alias deployment-inclusive
89T/16P/13G/0C. Removed0,added0,reclassified0. L159/L185 and L181 remain.
The owner's premise-removal completion criterion is NOT achieved.

## Proved findings

ARR_OracleCoverage.exact/digest_iff, ARR_ReturnCoverage.iff_returns:
under the retained returning-value interface, reached-read representation is
certified exactly when every actual attempted syscall returns successfully.
Pure source rejection, early exits and divergence steps remain covered.
The literal digest helper's original result equals its ideal result iff the
native syscall returns the encoded answer of that H. RuntimeSyscall alone
allows a failed syscall. ARR_OracleLoss.digest_loss/cost_loss are precise
source-helper diagnostics, not installed accepted attacks.

ARR_PrefixCost.suffix/native_le_ideal/same_cost_iff_empty uses the exact RPx
attempted-prefix theorem: ideal addresses = ALL native attempted addresses ++
remaining, including a failed call; ideal count = native count+remaining.length.
An upper bound is not promoted to original-cost equality.

ARR_OffPath.factory_forces_reads is the main new finding. For a fixed hashv,
the acceptance-guarded global factory
`∀ K, accepted(K) → ∃ sha256, P1 sha256 K ∧ RuntimeSyscall hashv sha256`
requires EVERY address where that native hash returns to be queried in EVERY
accepted run. A single returning address outside one run's finite query log
produces an incompatible world with the EXACT SAME evaluation, adaptive choices,
original work and outcome. Acceptance alone cannot exclude that world.

ARR_FactoryLoss.same_execution preserves ANY predicate of the complete run.
Its bounded_no_factory refutes that schema for a nonempty accepted class with
uniform issued budget N<256^32 if hashv returns on every valid one-part 32-byte
message. This return32 condition is explicit, NOT approved new runtime trust,
and NOT established here for the pinned native implementation.
The finite-cardinality proof is symbolic: after direct072 reached the default
recursion limit, ABSTRACT ARR_FiniteFresh.missing was tested073, its State
instance074, then consumer075. No cap/depth option increased or huge universe
enumerated.

ARQ_WorldSupport.Supported projects this global factory through each
NativeAt.sha256/p1/syscall. Thus a proposed all-world native factory needs an
execution-indexed interpretation or a proved on-reached-call/ROM transport,
rather than silently requiring a fixed native dictionary's answers outside
execution. The concrete account specialization was not compiled because its
cached closure is missing. No full Rc10 logical independence, actual deployed
attack, native return32 proof or whole-game exclusion classification is claimed.

## Requested coverage/carrier/composition and non-vacuity

All-world bank-supported deployed representation, deployed-carrier
identification, adaptive original-cost/outcome-law coverage and the new actual
top remain OPEN. The attempted SCE/account and bank modules could not load
Port1_CanonicalHeadline. Uncompiled drafts are explicitly *_PENDING.lean.txt
in this directory, not imports or accepted modules in lean/.
No all-world support, collision bound, source acceptance or desired conclusion
has been hidden as a new trusted hypothesis or given premise-removal credit.
ARQ's existing direct-account/raw/recovery/domination results remain inherited;
they were not freshly recompiled or installed at a replacement top here.

ARR_CoveredExamples only establishes nonempty MODEL reached-read certificates,
including pure rejected steps. It is explicitly NOT joint headline non-vacuity.
The complete real-byte extracted-wrapper pair remains pending. Read-only git
inspection (no foreign worktree access or edit) found:

- JFp branch codex/cx-joint-fixture10-20261026 at f0c8fd2634: exact proved partial
  targets AspisR1.JFp_SHABlock00.checked through JFp_SHABlock24.checked and
  AspisR1.JFp_SHA256.blocks_chunks. No complete native accepted pair theorem
  exists in that inspected commit.
- JFo branch codex/cx-fixture-tx2b-20261026 at629d8bb813: exact partial consumers
  AspisR1.JFo_Tail.source and AspisR1.JFo_Tail.native. They prove the real reader
  tail, not the full jointly inhabited extraction/native/game/persistence tuple.

The existing conditional ARQ_FixtureRecovery.composed consumes a supplied SAME
real-byte native pair, game, extraction, admissions and persistence witnesses.
No newer complete JFp/JFo theorem name is invented or assumed. Supplying that
pair still does not prove the all-world factory or original-law representation.

## Resource, verification and frozen artifacts

Final receipts and exact totals are in ARR_VALIDATION.json and ARR_attempts.jsonl.
All compiler invocations use the unchanged SInt2 host launcher/cache workspace,
one own scope at a time, MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64,
Lean-j1-M7000-async=false. Every receipt records target/command, revision plus
source snapshot/hash, selected direct import-object hashes, exit, wall, peak RSS,
swap, cgroup limits and full axioms/errors. Failed outputs are excluded.

Missing unchanged dependency inputs were compiled individually as expressly
authorized, with exact canonical source snapshots and no foreign source edits.
ARR_MISSING_CACHE.json is a source-graph overapproximation, NOT a fresh kernel
closure manifest. New ARR proof scopes reuse the retained objects; no package
or full-manifest replay, Kani, Rust, Aeneas or SBF build ran.
Prelaunch002 found missing OraclePortFrozen2Headline and launched NO Lean;
its failed local collection is retained. No launcher/admission infrastructure
was repaired. The local dependency queue was intentionally stopped after070
finished and all child receipt collection completed; no host proof was killed.

No shipped Rust/cfg(kani)/parameter/feature/wire change, so no ELF rebuild
trigger. Inherited pins, NOT freshly reproduced or rehashed:
- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

No session A worktree/candidate, foreign prefix module, key, wallet, balance,
authority or funds was touched. No object, binary, ELF or archive is committed.

## Final validation and budget stop

Budget EXHAUSTED: 100/100 actual Lean invocations,0/0 Kani.
90 pass,10 excluded failures;79 missing unchanged dependency builds.
Label002 is the sole prelaunch-only label. No further compiler invocation.
All27 new theorems were checked and axioms-printed in final target
ARR_FinalAudit.lean (101): exit0,wall2.216972825000994s,
peakRSS5267712KiB,swaps0,revisionb45f544adc010e06ceae81f8556851411154dc0a
plus exact dirty-source hash 7a7dac727dce8e5b8038e039f1519ef7239730ee237097675b275acc4121e4e5.
All printed axiom sets are subsets of propext/Classical.choice/Quot.sound.
Total actual Lean wall179.90244749881094s;maximum RSS5293604KiB;swap0.
ARR_validate.py --final passes source/snapshot hashes, standard axioms, caps,
budget, unchanged root, forbidden-proof-token scan and the atomic ledger recount.
ARR_HOST_MANIFEST.json freshly pins all90 passing source/object pairs and
sidecars in the reused workspace; it is NOT a coherent full release rebuild.
The exact next unbuilt source-graph predecessor after this restoration is
RRNodeTariffM10; Port1_CanonicalHeadline remains unavailable at the root.
The source graph remains an overapproximation of kernel imports.

No live own compiler scope remains. Shared pinned cache objects are retained
for reuse; no duplicate workspace, Rust target, solver temp or object-scratch
directory was created. Only ARR_ proof modules and this task's evidence are
committed. All stage commits remain local, with plain messages.
