# NLF SDK borrow law handoff

**Target not yet established.** Reusable (be)(2)/(au) SDK support packet supplied;
no native entry/Pool driver closure and no ledger promotion. Baseline ledger20
remains560 CLOSED /0 QUALIFIED /39 OPEN of599. Branch
codex/cx-sdk-borrow-20261107; commits only, no push.

## Established and precise scope

Import NLF_SdkBorrowLaw. Complete shared/exclusive SDK data and lamport wrapper
Results, selected cell/payload, error mapping, scalar getter Drop/panic,
metadata projection/frame, current Ref/RefMut projection, move/drop and token
consumption laws compile. The complete per-cell ledger excludes NJN-F2's duplicate
writer; globally fresh monotone tokens exclude cross-cell ownership duplication.
Acquisition/deref/release and source-ordered folds preserve ownership, and
admitted_counter_range derives -1 <= flag <= 2^63-1 from runtime admission.

Three-account TX1 snapshots/exclusive-copy and seven-account TX2 sequential
snapshot acquisition/cleanup are parent-state token-event laws. All ten source
occurrences have explicit packets. Every reply/error, SAME cell and payload,
lexical Drop, key/alias identity and zero-counter/liveness premise is retained.
The copy law composes ONE native byte window at arbitrary offset/observer over
1768 arbitrary bytes with canonical KMX induction; it also retains borrow Err
and unequal-length abort prefixes. See NLF_LAWS and NLF_CUTS for exact statements.

Actual pinned SDK wrapper code runs in Kani with safely created typed guards;
no Ref/RefMut-returning function is stub_verified. ScalarReply fidelity controls
all behave as required. This is the approved thin-wrapper transcription over
existing std semantics, NOT universal unsafe RefCell verification or a new
native whole-parent certificate. The native safe-constructor domains and the
universal std interpretation are distinguished in NLF_CORRESPONDENCE.

## Validation and trust

Final combined import loads NKW ledger20 + NJN + AspisR1.RPx_Deployed.deployed.
L079:189 raw roots, standard axioms only. Same compiled proof binary/eight
fixtures pass; L080 NFX-style scan exit0 across16430 modules,
751649 declarations/26809844 references:zero dangling,
incompatible owners or import defects. Two combined audits total. This is a
focused cached cohort, not a cold release replay. Full33023
selected object/sidecar pins include the Aeneas library actually resolved.
L084/L085 retain full machine-elaborated wrapper/consumer statements with all
implicit arguments shown. These two review modules declare no new constants
and do not change the audited semantic import or require a third combined audit.

Budget60/60 native attempt IDs:{'NATIVE_PASS': 17, 'MATCHED_FAILING_CONTROL': 19, 'COMPILE_OR_CODEGEN_REJECTION_NO_CREDIT': 24}.
Compile/codegen rejections earn no credit; own queue repair and every failed
step are retained.73/90 Lean compilations;85 total non-Kani scopes (73
Lean compilations, 12 link/audit/inspection scopes),0/0 extraction.
All scoped admissions exit0 AND allowed:true; disk >=40GB before each scope.
Caps6G/8G/swap0/tasks64,Lean-M7000,one scope at a time,optimized/offline Rust.
PeakRSS7703684KiB,scope wall875.847s,swaps0.
No timeout,memory kill,cap increase,unchanged retired rerun or heavy field gate.
Each receipt records target,argv,source revision/dirty snapshot and hashes,
dependency pins,exit,wall,RSS,swap,limits and printed axioms(native:N/A).

SDK pins:solana-program2.3.0,solana-account-info2.3.0,ProgramError2.2.2;
core source/deployed and Kani compiler versions are separately pinned.
Before EVERY native attempt the resolved frozen lock graph is checked offline;
all60 post-run locks remain byte-identical. Final SDK bytes/source/lock and
both programs' SDK dependency closures match. Frozen Pool's new Cargo.toml is
byte-identical to the old manifest; Pool parent bodies were NOT native targets.

Ten per-wrapper ReviewedTranscription items are option-A P6/D188
RECLASSIFICATIONS,never removals. No new runtime row or headline premise
discharge. Existing std semantics, runtime admission/native relatedness,
allocator and physical/source/ELF trust remain. RuntimeCpiReadonlyEntry7 is
PENDING and unused. Frozen3,L154 parameter,narrowed D188,100-bit PER-ATTEMPT,
privacy and the two-transaction contract are unchanged.

## Reuse and remaining work

Own workspace /home/dombarker/project-offloads/codex-cx-sdk-borrow-20261109;
CARGO_TARGET_DIR there as NLF_target. Seeds copied FIRST NJN1099008bytes,
THEN NKW1365368bytes; individual hashes retained. No shared cache writes.
Final export:/home/dombarker/project-offloads/codex-cx-sdk-borrow-20261109/NLF_exports_20261109_72e6c5ce1014 (3436632bytes).
Prepend that export,NLF_seed and the remaining L078 LEAN_PATH; use the full
NLF_CLOSURE_PINS manifest to reproduce selected objects. Own cache/TMPDIR,
source snapshots and exports retained. Host free98984427520bytes;
own workspace1366639307bytes (<30GB). No key/fund/authority action.

Remaining entry/Pool parent cuts must bind these primitives at SAME native
arguments and related runtime heap, construct owned snapshot Vecs, instantiate
actual child packets and retain ordered effects/abort/cleanup. TX1:094 and
Clock/PDA/authentication/Pool continuation work are not silently assumed.
An allocator/copy/caller abort inside a loan must stop at its acquire/deref
prefix with the guard live; SnapshotFold's completed-scope restoration must NOT
be used as an allocator-success premise or a Drop-after-abort event.
Member-by-member obligations are in NLF_REMAINING; no Lean-only SDK law was
left merely because native allowance was exhausted. Unused formal allowance
is not reported as impossibility or exhaustion.

No shipped source or existing proved module changed. Harnesses are committed
as NLF_native_packets.patch plus exact receipt inputs; patch reverse-dry-run
matches K060 bytes. No ELF rebuild trigger. Verifier pins f8c0ec72…/63ad3e9c…
are inherited; latest owner-amended Pool pin is e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc
at b936275465,not the historical121f… in predecessor reports. No fresh artifact
reproduction is claimed. No sessionA/sibling worktree touched.
