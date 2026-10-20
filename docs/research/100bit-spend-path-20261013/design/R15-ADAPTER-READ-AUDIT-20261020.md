# R15 adapter account-read audit (2026-10-20)

## Scope and decision

Source revision: `b7016bea9c308882c4f1753eb1c7892b33f479f7`, branch
`codex/cx-adapter-audit2-20261020`. Production verifier and adapter sources
remain frozen. This extends [the write map](R15-ADAPTER-WRITE-AUDIT-20261020.md)
under the LEAD-NOTE addendum “S6 re-pinned”: the adapter binding is a source
audit beside P2, not an AccountInfo extraction theorem. Pinned Aeneas cannot
translate `SliceIndexShared<AccountInfo>` at adapter :950; see
[REPIN-s6](REPIN-s6-20261020.md). No new extraction or Lean replay is claimed.

Paths below use `P/ = programs/r1-cost-probe/src/`,
`C/ = crates/aspis-r1-cost-probe/src/`, and
`S/ = crates/aspis-statement/src/pool_v1/`. Line numbers refer to the source
revision above. Release features are `pool-adapter,private-leaf-salts`, without
`cu-profiling` (observer is `None`, `P/lib.rs:35–39`). Ranges are half-open.

## Read table: stage 1, exact instruction [3,10]

The release guard `P/lib.rs:56–64`, `P/pool_route.rs:3–5` runs before any
account access. Adapter dispatch is `P/r1_pool_adapter.rs:1037–1042`.
All rows below refer to that adapter unless another file is named.

| Account/read site | Guards before data use, and validation at the read | Bytes reaching the verifier |
| --- | --- | --- |
| Account metadata, :947–956; helpers :191–233 | Exactly three accounts and exact instruction at :947. Account references :950–952 are in bounds. Pairwise **key** distinctness at :953 precedes all data borrows. Proof/public must each be non-signer, read-only, non-executable (:954–955); their owners are deliberately unrestricted. Checkpoint must be owned by `program_id`, non-signer, non-executable, writable, exactly 1,768 bytes (:956, helper :210–221). `try_data_len` itself is a checked SDK read. | Metadata is used only for guards; no AccountInfo, key, owner or lamport balance is passed to the core. |
| Verifier checkpoint index 2, mutable borrow :957; full scan :958 | Metadata/length/distinctness above. Every byte must be zero; otherwise AccountAlreadyInitialized. Mutable borrow is held through verification and copy. | Existing bytes are **not** an input to tx1. Returned checkpoint vector is length-checked then copied in full at :982–985. |
| Public buffer index 1, immutable borrow :961 | Previous guards and zero checkpoint. Entire raw slice is decoded at :962 via :236–243. `S/pair_forest_terminal.rs:400–420` first requires exactly 1,880 bytes, ASF8 magic/version/kind/digest encoding, then decoded common/public layers; adapter :963–964 validates the statement. No lifecycle header is stripped. | The **original full borrowed 0..1880 bytes**, not a re-encoding, are passed as `&public_data` at :981. `statement.semantic_public()` is a projection of the object decoded from this same immutable borrow. |
| Proof buffer index 0, immutable borrow :970 | Previous guards and valid statement. Statement candidate is encoded into a local vector at :965–968. Checked `688 + 57607 = 58295` at :971–975; exact total length is tested before prefix/tag indexing. Prefix `0..688` must equal that candidate encoding; byte 696 (`688+8`) must be S2 (:976–979). | Only **proof_data[688..58295]**, exactly 57,607 compact proof bytes, is passed by immutable subslice at :981. Prefix is checked but excluded from the proof digest. |

`P/r1_pool_adapter.rs:981` calls `first_decoded(semantic_public,
&public_data, &proof_data[688..58295], 10)`. The adapter does **not** call
`first`. `P/lib.rs:42–50` shows that `first` would decode those supplied public
bytes and delegate to exactly `first_decoded`; the latter calls
`verifier::tx1(public, public_bytes, proof, k, SolanaDigest, None)` without
copying/replacing either byte slice. Both immutable account borrows remain
live throughout tx1. Core re-export `C/verifier.rs:515–517` selects
`C/candidate.rs:270–290`: shape/canonical scan, preparation, first ten queries,
then `checkpoint(&p, &a, proof, public_bytes, hash)` at :288 on the original
slices. The successful returned vector alone becomes account index 2.

**Stage-1 conclusion:** accepted `[3,10]` binds decoded semantic public to
the exact original public bytes and the exact guarded compact-proof subslice
used by tx1 and its checkpoint writer. No other account data is read. Stage 1
does not authenticate Pool/registry state; that occurs at stage 2. The other
admitted stage-1 spelling `[3,11]` has the same account reads/guards but fails
`k != SPLIT` at `C/candidate.rs:271–273`, before checkpoint creation/write.

## Read table: stage 2, ASQ8

Stage2 requires seven accounts and ASQ8 magic (:995–998). `validate_asq8`
(:885–919) requires the exact request length, successful request decoding,
frozen profile/release/Pool bindings (:891–900), derives the requested output
lane from the nullifier (:903–904), and obtains `Clock::get()?.slot` (:910).
The clock is a **sysvar syscall**, not an eighth AccountInfo. Instruction
payment fields and bindings are transaction instruction bytes, not account data.

All seven keys are pairwise distinct (:693–701) before any account payload
is decoded. Helper `require_readonly_account` (:170–185) requires expected
owner, non-signer, non-writable, non-executable. Raw proof helper (:191–204)
has those three flag checks but no owner constraint. Owner/flags/distinctness
are runtime-supplied metadata; stored-bump PDA checks occur **after** decoding,
not before borrowing. Borrow failures propagate as errors.

| Index / payload read site | Checks before read; checks made on decoded data | Contribution to core inputs |
| --- | --- | --- |
| 0 raw proof, :912–913, again :1007 | Read-only raw buffer :688; all keys distinct. `scan_proof_buffer` :780–805 first checks exact 58,295-byte length, then decodes canonical candidate `0..688`, re-encodes and compares it, and checks S2 tag at byte 696. Repeat borrow :1007 follows all authentication/reconstruction; exact length is checked again :1012. | Candidate is copied into the reconstructed statement. Core receives only immutable **688..58295**, at :1022. No ASPU header, lifecycle tail or owner-specific bytes are used. |
| 1 Pool master, :703 | Pool owner and read-only flags :690; distinctness :693. Whole slice to :429–433 → `S/pair_forest_accounts.rs:261`, which length-checks 384 bytes before header/field decoding. Checks identity.pool equals key, all lanes initialized, and stored-bump master PDA from asset mint (:704–716). Policy is validated and pinned to immutable registry, registry program, zero authority and audit policy (:535–544). | Copies account key, asset/deployment identity and policy into authenticated local objects. Asset id must match request (:867–872); deployment domain and live lane data enter the statement, not raw master bytes. |
| 4 registry, :551 (v2) or :619 (v1) | Read-only registry owner :546; seven-way distinctness already done. Full slice to versioned decoder: `S/verifier_registry.rs:425` first checks 256 bytes (v2), :279 checks 128 bytes (v1), then format/reserved/field validation. Registry PDA uses master key/stored bump; pool/authority/policy, immutable and unpaused checked (:553–579 or :621–639). V2 also pins loader, registry program and derived ProgramData address. | Authorization only; no raw registry bytes enter verifier. ProgramData **addresses** are derived; no ProgramData or executable account payload is read. |
| 5 release entry, :582 (v2) or :642 (v1) | Registry validation precedes entry read. Read-only registry owner :581/:641. Versioned decoders `S/verifier_registry.rs:513` / :347 first check 320 / 192 bytes. Stored-bump entry PDA includes master/profile/release. Pool/policy/verifier id/profile/release/statement version and active-at-clock-slot checked (:584–615 or :644–667). V2 also pins loader/derived verifier ProgramData and zero expected upgrade authority. | Authorization only. No entry bytes or executable image is passed into core. Canonical stored bumps rely on owning initializer provenance; address derivation does not independently search for the canonical bump. |
| 2 historical **Pool checkpoint**, :728 | Read-only Pool owner :691; distinctness. Full slice via :436–440 → `S/pair_forest_accounts.rs:426`, checking exactly 192 bytes before decoding. Master key/domain and stored-bump PDA including sequence checked (:729–742). | Copies key, sequence, global root into reconstructed common statement (:815–820). This is distinct from verifier checkpoint index 6. |
| 3 selected Pool lane, :744 | Read-only Pool owner :692; distinctness. Local decoder :448–519 checks exact **768 bytes** (`80 + 48 + 32*20`, `S/pair_forest_accounts.rs:30–32`, `S/incremental_merkle.rs:27–29`) before indexing, format binding, magic/version/lane count/depth, reserved bytes, nonzero master, nested tree header, capacity, canonical root/frontier, empty subtree roots. Lane master/id and stored-bump lane PDA checked :745–758. | Copies lane key/id and live snapshot (master key, domain, sequence/next index, root, frontier) at :760–775; these become statement common/live fields :814–825. |
| 6 **verifier checkpoint**, metadata length at :689, payload :1008 | `require_verifier_checkpoint(..., false)` requires verifier owner, non-signer, non-executable, **read-only**, exactly 1,768 bytes (:210–221); distinctness precedes payload borrow. All ASQ8 checks have succeeded before :1008. | Full immutable **0..1768** slice passed at :1023. `resume` checks header/status/reserve/variant and rehashes before decoding state (`C/verifier.rs:393–400`). |

There is **no stage-2 public-buffer account**. Request payment fields are
copied into transfer/withdrawal statements (:829–853, :874–881); authenticated
common fields and proof-prefix candidate are copied at :814–825. Reconstruction
requires candidate.next_pair_index = live.next_pair_index + 1 and matching
asset id (:862–872), then validates the full terminal statement. At :1015–1019
that statement is encoded into a fresh **1,880-byte local vector**. At :1020–1026
`tx2_authenticated(&public_bytes, &proof_data[688..58295], &checkpoint_data,
SolanaDigest, None)` receives exactly these three immutable slices.
`C/candidate.rs:327–330` shape-parses the proof, then :294–295 passes the same
slices, with argument order checkpoint/proof/public, to `resume`. No intervening
adapter copy changes proof/checkpoint bytes. Reconstructed public bytes are
new storage; same-byte binding means **byte equality**, not pointer identity.

**Stage-2 conclusion (both transfer and withdrawal):** every AccountInfo
payload read is in the seven rows above; all raw buffers remain immutable
through the verifier call. The public re-encoding is accepted only if its digest
matches the stage-1 public-byte digest in the verifier checkpoint. Altering a
public account after stage 1 does not by itself affect stage 2, because that
account is absent; altering the reconstructed public input does. No account
lamports are read, no CPI/executable/ProgramData payload is read, and the only
additional runtime read is the Clock sysvar. Successful return-data encoding
(:923–941) uses the local validated statement and performs no new account read.
Lifecycle and legacy routes are excluded by the release guard before account
access, as enumerated in the write audit.

## Same-byte binding and precisely labelled proof evidence

The frozen source writer `C/verifier.rs:326–340` stores
`SolanaDigest([proof])` at checkpoint **16..48** and
`SolanaDigest([public])` at **48..80** (:329); its checksum covers the preceding
checkpoint bytes with domain `UNPROVED:R1:checkpoint` (:339), and occupies
1736..1768. `P/lib.rs:10–15` implements the backend with `hashv(parts).to_bytes()`.
At stage 1 the proof is the compact suffix, public is the original full ASF8
borrow. The candidate prefix is excluded from the proof hash but must equal
the public statement's encoded candidate (:976). At stage 2 that prefix is
canonically scanned and copied into reconstructed ASF8, so changing it changes
the public binding rather than the proof hash.

`C/verifier.rs:393–396` checks checkpoint size/header and compares precisely
those stored fields with freshly computed singleton proof/public digests,
then checks the domain-separated checkpoint checksum. These are the exact
proof/public arguments delivered by :1021–1023 through candidate :295.
No different serialization is substituted between the core entry and resume.
Matching digests give byte equality only under the existing hash/backend
assumptions (P1/P3); the unkeyed checksum alone establishes no provenance.
Owners of the foreign raw buffers are unrestricted and read-only flags lock
only the current transaction. The audit does not infer unconditional
cross-transaction immutability from these flags or require identical account
addresses across the transactions.

| Evidence status | Exact fact and boundary |
| --- | --- |
| **Checked stage-2 digest fact, inherited** | `evidence/stage2-continuation-20261020/proofs/resume-fact-v6/source.lean:31`, `AspisR1Stage2.resume_rehash_checkpoint_field`, with adjacent `receipt.json` and `lean.log`; `proofs/final-binding.json` ties the full emitted resume adapter to final extraction. Successful complete emitted resume implies the stored **16..48** proof field equals the singleton proof digest, with universally quantified typed operations and explicit comparison-soundness premise. Receipt: exit 0, standard axioms `[propext, Classical.choice, Quot.sound]`. This is a proof-field fact; it is **not** a proved public-field preservation or SDK AccountInfo theorem. The public **48..80** comparison here is audited frozen source at :396. |
| **Parked writer length, not adopted** | At parked revision `92e30def94f94b0e400cbd96fba4a94fe485fd48`, `evidence/freeze-prep-20261020/proofs/checkpoint-length-v1/{source.lean,receipt.json}`, `AspisR1Tx1Finish.checkpoint_success_length`: successful complete emitted writer has emitted checkpoint_size, over parameterized typed helpers. This is the parked serializer-loop refactor, not an adopted frozen-writer theorem. |
| **Parked reachable determinism/digest facts, not adopted** | Same parked revision, `evidence/tx1-finish-prep-20261020/proofs/checkpoint-facts-01/{source.lean,receipt.json}`: `checkpoint_reachable_determinism` (:15) assumes the same successful preparation on the same bytes, accumulator, backend and operations; `checkpoint_writer_proof_digest` (:29) records the singleton proof digest call; `successful_writer_resume_share_proof_digest` (:51) joins successful writer **and successful resume** plus comparison soundness to stored 16..48. Neither proves unconditional helper preservation or public-field preservation. |

`evidence/freeze-prep-20261020/FREEZE-CANDIDATE.md` on that parked revision
explicitly says “retained unmerged, not adopted.” The parked files are absent
at this base; read-only `git show` pins (revision/path/SHA-256/size) are retained
in this job's `parked-writer-references.json`. No parked verifier change or
proof is silently merged or transported to the freeze. The earlier write map
contains the complete checkpoint byte layout and the same writer limitations.

**Exact remaining account-boundary premise:** P2 (the runtime enforces
ownership, signer/write permissions, locks, atomic rollback and persistent
writes, with the audited exclusive admitted checkpoint writer), plus
**“the runtime presents the same account bytes to both transactions when the
checkpoint digest matches.”** Here “same account bytes” means the complete
compact-proof suffix and complete public verifier input; stage 2's public
input is the reconstructed encoding rather than a public AccountInfo. It
does not assert raw Pool/registry images equal stage-1 account images (stage 1
has none), nor that pointers/account keys must match. The checksum is not a
MAC; authentic checkpoint provenance still requires P2 and the write map.
The existing named hash-collision/backend assumptions remain in force.

Under this stated boundary, the S6 caller binding is discharged by the source
map: same immutable public bytes supply decoding/semantic projection and
checkpoint hashing; the guarded compact suffix supplies tx1 and checkpoint
hashing; resume rehashes the stage-2 inputs against those fields. This leaves
R15's unconditional writer/helper refinement and complete reachable-state
cross-transaction proof obligations open. It does not promote them to proved.

## Executable teeth and receipts

Packet: `evidence/r15-adapter-read-audit-20261020/`. The only Rust delta is two
tests appended to `P/r1_checkpoint_tests.rs`; no verifier/adapter production
body, fixture, manifest or SBF artifact changes. Host workspace is the independent
`/home/dombarker/project-offloads/codex-cx-adapter-audit2-20261020/` source/cache
copy. `input-hashes.json` and `source-validation.json` verify all **228** selected
source/manifest/fixture files against this worktree. All 57 production/other
entries of the freeze's 58-file inventory remain identical; its only changed
entry is the existing test file. No key creation, transaction, refund or cleanup
occurs.

```
cargo test --release --offline --locked -j 4 \
  -p aspis-r1-cost-probe-program --features pool-adapter,private-leaf-salts \
  --lib r15_read_ -- --test-threads=1
```

| New host test | Observed result |
| --- | --- |
| `r15_read_binding_rejects_account_buffer_changes_after_stage1` | Produces checkpoint via actual release `[3,10]` on AccountInfo buffers. Unchanged proof/public pass resume and authenticated tx2 (positive controls). After ending account borrows, flips one compact-proof byte in the proof account: both calls reject with `Error::Checkpoint` after exactly **1 hash**. Restores proof, flips a public-buffer byte: both reject with `Error::Checkpoint` after exactly **2 hashes**. Checkpoint bytes stay unchanged. Public mutation tests the resume input contract, not a nonexistent stage-2 public account. |
| `r15_read_stage1_rejects_wrong_lengths_and_non_distinct_accounts` | Actual release `[3,10]` rejects each proof/public/checkpoint buffer one byte too short and too long (six cases, `InvalidAccountData`), and all three duplicate-key pairs (`InvalidArgument`). Every account's bytes/lamports remain unchanged. |

Result: **2 passed, 0 failed, 0 ignored**, 37 filtered out; test runtime 0.00 s.
`receipts/read-teeth/{receipt.json,stdout.log,stderr.log,time.log}` records
build+test exit **0**, wall **4.611 s**, peak RSS **260,912 KiB**, swaps **0**,
exact command/environment, base revision plus hashed test delta, cgroup peak
and actual limits. Scope: `MemoryHigh=6G`, `MemoryMax=8G`, `MemorySwapMax=0`,
`TasksMax=64`, four Cargo jobs/four linker threads. Expected time was incremental
release compilation and two tests, with no proof generation/elimination.
`#print axioms` is N/A: no Lean work.

Resource snapshot `reservation.json` used the inherited `run-*.scope` scanner
(retained as `reservation-initial.py`): it saw 15 GiB bounded reservation,
plus this job's 8 GiB, below 55 GiB. That scanner omits custom-named scopes;
its snapshot is not a complete reservation proof. The corrected `reservation.py`
scans **all** scope names; `reservation-all-scopes-post.json` records zero
populated scopes after this short test run. `run-host.sh` now uses that broader
preflight for any future source-changing run. This correction triggered no
unchanged test rerun. The actual job cap is independently checked inside the
scope by `capped.py` and recorded in its receipt.

These native checks exercise real SDK AccountInfo wrappers and the frozen
core on a saved transfer fixture. They do not establish Agave metadata
provenance, historical account immutability, cryptographic collision resistance,
or a full stage-2 ASQ8 execution. The existing candidate-reconstruction test
and write-audit runtime/SBF evidence are inherited; this job does not rerun
unaffected suites or claim a new runtime measurement. Withdrawal shares the
same audited buffer/digest path, but no new withdrawal fixture test is claimed.
Validate this packet without rebuilding with:

```
python3 -B docs/research/100bit-spend-path-20261013/evidence/r15-adapter-read-audit-20261020/packet.py --check
```
