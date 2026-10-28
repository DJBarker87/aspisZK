# PDA handoff

Branch: `codex/cx-joint-pda-20261028`. New JHs modules only; no push.

## Claims and boundaries

The pinned SDK path and exact byte layout are documented in JHs_PDA_SPEC.md.
Cached SDK source is independently compared byte-for-byte with the matching
crate archive; all four archive SHA256 values match the frozen root Cargo.lock
checksums (JHs_SDK_ARCHIVE_CHECK.json). No validator runtime is pinned by this
program lockfile. The native caller has **seven** reached PDA calls: three
outer authentication calls and four immutable-registry calls. The requested
four-call reading would omit obligations; all seven are retained here.

`JHs_PDA.derive` is a uniform mathematical model using the existing
`JFp_SHADigest.digest`, ordered seeds/program/marker, and the Edwards25519
square-root-existence predicate `OnCurve`. Its guard/error theorems establish
seed count and per-seed limits, curve rejection, certified success, caller
error mapping, and SDK syscall return-code interpretation. They do not prove
native source/syscall/dalek equivalence. `FixturePdaRuntime` is proposed in
JHs_TRUST_PROPOSAL.md for the OWNER; it is **not adopted**.

`JHs_Inputs` proves each actual fixture preimage and seed bound.
`JHs_SHA{Master,Checkpoint,Lane,Registry,RegistryProgramdata,Entry,VerifierProgramdata}`
check 16 SHA blocks using one-round transitions, explicit padding and symbolic
block aggregation. The generator's --check passes. Exact byte arrays, seeds,
program IDs, input lengths, digests and expected keys are in JHs_CALLS.json.

`JHs_FixtureCertificates.SHARealization` names the seven exact digest equations.
`OffCurveCertificates` names seven exact propositions on the corresponding
concrete digest bytes; it has no callback-success/decoder/acceptance fields.
Off-curve certificates remain **unproved**. The equation model deliberately
adds neither canonical-encoding restrictions nor subgroup checks. Its
correspondence to dalek's actual decompressor remains an explicit obligation.

## Integration status

`JHs_DigestEquations.realization` now **proves all seven SHA equations**;
no digest-value hypotheses remain in `JHs_InstalledPDA`. The latter installs
`op38 := JHs_PDA.derive` uniformly for every input and proves the exact seven
reference-slot observations from `OffCurveCertificates` alone. Both final
modules compiled successfully (JHs_024/JHs_025), standard axioms only.
The installer is a mathematical candidate, not a claim
that the opaque external SDK declaration now has an extracted implementation.
The three outer observations have exactly the seeds, programs and expected
keys of JHj_Authentication.source. Four more observations serve its registry
child. No authentication/decoder result is assumed inside any certificate.

## Validation and resource record

**25/40 Lean attempts; 12 accepted compiles covering all 12 new modules.**
JHs_024 (digest equations): exit 0, 5.819090845 s, peak 5,783,940 KiB, swap 0.
JHs_025 (installed bridge): exit 0, 2.662876193 s, peak 5,712,180 KiB, swap 0.
Maximum measured process RSS across all attempts: 5,783,940 KiB (5.516 GiB).
Every accepted theorem audit is a subset of propext, Classical.choice and
Quot.sound. `choice` in the first module's output is the opened Classical name.
JHs_FOCUSED_MANIFEST.json matches every final source hash to its successful
compile receipt; JHs_FINAL_SOURCE_AUDIT.json verifies every theorem has an audit.
JHs_024's refused admission did not consume an additional Lean attempt.

Raw per-attempt source snapshots, stdout, time and dependency/source hashes
are retained in JHs_*/receipt.json; JHs_ATTEMPTS.jsonl distinguishes failed
attempts from accepted evidence. Failed elaborations can print `sorryAx`:
those outputs are rejected and carry no theorem credit. Accepted module audits
must use standard axioms only. No sorry/axiom/admit/native_decide is in source.
No Kani, package-wide build, Aeneas replay, SBF rebuild or full frozen manifest
was run. Focused compilation reuses the assigned copied cache and pinned
inherited dependency paths. This is not a full release replay.

Each launched Lean command uses lake env lean -j1 -M7000, one admitted scope,
6G/8G, swap max 0, TasksMax64. Source revision and dirty source hashes are
recorded per attempt. JHs_012's copied source_revision field is stale; actual
base is b2e627900b (dirty new source), explicitly corrected in the index.
The initial admission retry waited 76 seconds rather than the prescribed 180;
this cadence error is recorded. No process launched on a refused admission.
The later JHs_024 refusal waited 193.583 seconds before successful admission.
No timeout or memory kill occurred; failed proof inputs/generator cells were
changed before retry. Recursion/heartbeat/resource limits were never raised.
Own cache was seeded by copying codex-cx-fixture-cache-20261027, without changing
the seed, and is retained at /home/dombarker/project-offloads/codex-cx-pda-cache-20261028.

## Remaining owner/lead work

Decide the exact narrow proposed trust row, or provide proved syscall and
curve correspondence. Prove/authorize the seven off-curve facts, pin the
actual deployed runtime/ABI and artifact, then compose the model selection
with the real decoder/registry children. This task does not close those
children, TX2 acceptance, joint non-vacuity or the deployed security target.
Per ruling (s), soundness quantifies op38 and receives no new assumption or
credit from these fixture results. No wallet/key operations occurred.

## Stage commits

- 89c0872db3 — Specify pinned PDA path and propose fixture trust boundary.
- b2e627900b — Prove PDA guard and certificate structure.
- 723a389c56 — Check all fixture PDA digests and install the conditional model.
- Final handoff/source-pin amendment is the following documentation commit.

No existing proved module or frozen Rust source changed. Source snapshots of
failed attempts are intentionally retained as rejected evidence. All accepted
modules have final matching source hashes. Evidence has no file above 20 MB;
no compiled objects or binaries are committed. Worktree/cache keys and funds
were untouched. The remaining blocker is **not SHA**: it is the seven off-curve
facts, runtime/dalek association and the separate decoder/registry composition.
