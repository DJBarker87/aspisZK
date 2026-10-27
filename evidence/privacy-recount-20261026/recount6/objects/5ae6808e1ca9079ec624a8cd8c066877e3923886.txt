# pv-alib resume3: audited source/library candidates

Worktree **exactly** `/Users/dominic/ZK/.worktrees/pv-alib`; branch
`codex/pv-alib-20261027`; resume base `828c0ce4af884d1c7e062bd3d995b3c3603aec8b`.
**Target not yet established. No deployed endpoint premise was removed.**

The three assigned rows now have audited, cached-replayed **CLOSED-ON-CANDIDATE**
results at the specified source/library-law boundary. This does not certify
whole-machine native refinement, a coherent full release rebuild, or installation
in `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed`.

## Required recovery and checks, performed first

52775's existing `runs/52775/output.log` and `time.log` were recovered read-only.
Its five axiom reports are standard; its source was **never rerun**. The recovered
complete receipt is `52775.json`; `52775-INCOMPLETE.json` remains historical.

Before the first resume compile, every one of the coherent privacy replay's
5,673 external objects was SHA-256 checked, both at its authoritative manifest
path and at the object actually selected by this job's Lean path. All match.
The manifest SHA is `d9187c800b7479f66ec6147e3c8e91c1158d382c4aa467bf678e76901b9a8c0e`.
Evidence: `resume3-external-manifest.json`, `resume3-external-verification.json`.
No library object was rebuilt or substituted; no shared source was overwritten.

Project source resolution and the complete three-row source import cone are
recorded in `resume3-project-preflight.json`: 52 project modules, no missing
source authority or hash mismatch. The authority records are the EJR resolved
sources where applicable, CBL's committed SHA-pinned manifest9 source freeze,
and the committed candidate ProverRwFull provenance/source-manifest records
identified per module. Own new PV_AL sources are pinned directly. The two
initially absent MoveWorld/MoveSelected drafts were staged only privately.

The combined V233/V265 audit (37698) and one focused cached cone replay (37600)
were completed before V184 work. The audit has **159 standard axiom reports**;
the replay imports **41 project modules** together and checks every closing
signature. `resume3-candidate-cone.json` records the source cone; 37600's receipt
records all its directly imported object hashes. This satisfies the requested
candidate replay, not a full frozen-manifest or deployed endpoint replay.

## Row results and exact boundaries

### V233 / op209: provisional -> CLOSED-ON-CANDIDATE

Before: selected `split_blocks` source/value law for arbitrary representable
byte slices and link to the consumed callback remained `ProverRwFull.ExternalFuns.op209`.
The existing fixed soft digest did not supply this law.

After: `PV_AL_SplitSelected.native_callback` and `.consumed` give the complete
successful Result for the constructed native 64-byte trait/storage specialization,
for every input slice without a length bound. `PV_AL_SplitBridge.source_reference`
identifies the extracted reference observation and `.consumed_reassembles` proves
that the decoded blocks followed by the tail reconstruct the input. The generic
`PV_AL_SplitObservation.complete` includes division-by-zero failure for other
block sizes. There is no source-equality hypothesis; the actual native trait and
its size are constructed and proved. No SHA-NI semantics or V232 credit.

Audit/replay: 37698 / 37600, reconfirmed in the final 37699 audit. Reused native
and bounded no-stub Kani gates retain their original scope: 1,026 prefixes
through length 1025; arbitrary bytes/coordinates at lengths 0–129, unwind 132,
389 Kani checks. The extraction and fidelity scan are unchanged.

### V265 / op259: provisional -> CLOSED-ON-CANDIDATE

Before: the prepared selector lacked the native/reference source gate for
`ProverRwFull.ExternalFuns.op259`.

After: `PV_AL_CircleNative.source_reference` and
`PV_AL_CircleSelected.native_source` / `.consumed` cover every input block and
both rows with complete Result behavior. The structural gate preserves native
field calls, order, errors, fallback parameters and row selection; it does not
assume totality, arithmetic equality or source equivalence. Both row values and
carrier roundtrips are inhabited/proved. This uses ruling (k)'s structural route,
with no chained-field-arithmetic Kani run.

Audit/replay: 37698 / 37600, reconfirmed in 37699. Unchanged extraction,
`STRUCTURAL-CIRCLE-GATE.json`, fidelity scan and 8,712 native wrapper comparisons
are reused; `promote.py --check` passes. Bounded native measurements are not an
unbounded machine theorem.

### V184 / op33: OPEN -> CLOSED-ON-CANDIDATE

Before: the generic move-reference value law and zero-copy facts were proved,
but the native/world/selected bridge and frozen stdlib structural association
were missing. Recovery of 52775 establishes the native-value prerequisite.

After: `PV_AL_MoveWorld.source_reference` equates the native and move-reference
library executions on an explicit world. `.checked_observation` proves returned
last value, remaining dropLast contents, retained buffer and capacity, unchanged
allocation history/counters, data memory and arbitrary external frame.
`PV_AL_MoveSelected.native_projection` connects that observation to the selected
op33 callback; `.consumed` checks the actual extracted pop callback wrapper.

The closing theorem `PV_AL_MoveClosure.complete` combines both executions and
the consumed callback into one complete Result/observation statement.
`.allocation_delta` proves zero alloc/realloc/dealloc increments from arbitrary
initial counters and retains history. `.nonvacuous` constructs a full carrier
for every representable vector and address. Payloads are arbitrary Types with
no Copy/Clone bound. Buffer.fits is an ordinary length/capacity invariant,
satisfied by the explicit non-vacuity construction, not a hidden source law.

`STRUCTURAL-POP-GATE.json` pins and checks the complete nightly-2026-06-01
stdlib pop/remove/try_remove bodies. Their read/header/copy operations are
interpreted by the explicit Lean library semantics: last index bounds,
capacity assertion and zero raw-copy count are proved symbolically, for all
element widths including zero. The operations contain no allocator/destructor
call. Native raw remove is still unextracted: this structural/library association
is **not** a new unbounded Rust raw-pointer, compiler or allocator refinement.
No iterator/element restoration continuation is silently credited; the source
write classification and its boundary are recorded in the structural gate.

Reused gates: the 99-case pinned native allocation differential and 697-check
no-stub bounded Kani gate (12 unreachable checks, lengths 0–4, unwind 6).
New optimized `pop-zst-world-05`: **33 non-Copy Drop ZST cases pass**, with zero
allocator and destructor calls during either operation, retained pointers and
capacity. Rejected 04 had an ambiguous test-loop integer type; 05 changes it
to usize. Its failed receipt and source snapshot are retained. The old [17,29]
copy-reference allocation counterexample is retained as a failed approach,
never relabeled as a row counterexample.

Final audit/replay: 37699 / 37604. The audit covers **204 declarations across
all three candidate rows**. The V184 replay loads its **15 project modules**
from the verified cache and prints the three closing theorem axioms.

## Receipts

All Lean runs use -M7000, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64, one capped scope at a time. Every run below reports zero swaps.
Exact commands, full source revisions, source snapshots, dependency fingerprints,
full printed axioms and raw time/output/admission logs are in the numbered
receipts and `resume3-receipts.json`; aggregate history is `RECEIPTS.json`.

| Attempt | Target (R1Z/PV_AL_ prefix) | Exit | Wall s | Peak RSS KiB | Revision | Axioms |
|---|---|---:|---:|---:|---|---|
| 52775 recovered only | MoveNativeValue | 0 | 1.07 | 2637212 | 80c2e3cfda | 5 standard |
| 37697 | Rows233265Audit | 1 | 1.12 | 2622348 | 828c0ce4af | rejected audit: query names duplicated namespaces |
| 37698 | Rows233265Audit | 0 | 1.08 | 2630884 | 828c0ce4af | 159 standard |
| 37600 | Rows233265Replay | 0 | 0.97 | 2634172 | 828c0ce4af | signature checks; paired axioms audit 37698 |
| 37601 | MoveWorld | 0 | 1.11 | 2635704 | dda503c2ed | 9 standard |
| 37602 | MoveSelected | 0 | 1.10 | 2641956 | dda503c2ed | 5 standard |
| 37603 | MoveClosure | 0 | 1.15 | 2636400 | dda503c2ed | 3 standard |
| 37699 | FinalRowsAudit | 0 | 1.21 | 2631908 | e9c42631f3 | 204 standard |
| 37604 | MoveReplay | 0 | 1.13 | 2628560 | e9c42631f3 | 3 standard |
| native 04 | pop-zst-world test compile | 1 | 0.05 | 113536 | dda503c2ed | N/A Rust |
| native 05 | pop-zst-world test | 0 | 0.11 | 121432 | dda503c2ed | N/A Rust |

Standard means a subset of {propext, Classical.choice, Quot.sound}; the accepted
combined logs were parsed to check this explicitly. 37697 is retained and gets
no audit credit; no failed candidate lemma is treated as a row counterexample.
No sorry/admit/native_decide/implemented_by/axiom declaration was added.

## Accounting, integration and next deliverable

Resume3 used **8/25 Lean attempts**, seven accepted and one rejected, and **0/4
Kani runs**. Total history: 83 charged Lean attempts, 48 accepted complete
receipts, 35 rejected, zero incomplete; two of six Kani runs used. **17 Lean
attempts and 4 Kani runs remain.** Stopped at completion of all three assigned
scoped candidate rows and their requested audits/replays, not exhaustion.

Only **37600–37699** were used in this resume; 37697–37699 were audit IDs.
Historical 52700–52775 allocations conflicted with pv-batch3 and were invalid
cross-job reuse. They remain provenance evidence, never a justification to
reuse any 52xxx ID. Fresh range checks found no existing receipt/submission
hits before the first compile (`resume3-ID-PREFLIGHT.json`).

Endpoint assumptions removed: **zero**. Retained: deployment, whole-native
composition, E1/E2, real RunJoin and side-channel obligations around the deployed
endpoint. Added/changed: no endpoint premise, no T field, no observer or simulator
weakening. Changes are proof/evidence/reference tests only. No crates/ or programs/
file changed; no ELF rebuild or fresh pin verification is claimed. Inherited pins:

- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

After verification, own compiled objects were hash/size inventoried, then own
Lean/Rust target caches and two executable caches were removed under local-lean
rule 9. Sources, receipts, LLBC and extraction evidence remain; shared objects
were untouched. `resume3-cache-cleanup.json` records this. No keys were created,
removed or cleaned. No local Lean compile, full manifest replay, push or merge.

Next concrete deliverable: owner integration of these three source/library
candidate callbacks into the consumed native composition and deployed endpoint
conditions, retaining their stated primitive/structural and bounded-gate scope,
then the owner's coherent dependency replay and deployment audit. These scoped
results must not be reported as an unbounded whole-machine or deployed proof.

Resume commits before this final evidence checkpoint:
- `dda503c2ed` Audit and replay split and circle candidate closures
- `e9c42631f3` Connect move reference callback to explicit allocation world

`COMMITS.txt` records the source/proof history through that checkpoint. The prior
reports are retained in `REPORT-resume2-host-stop.md` and `REPORT-initial-stop.md`.
