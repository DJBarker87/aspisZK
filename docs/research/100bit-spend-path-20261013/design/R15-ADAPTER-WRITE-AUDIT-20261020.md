# R15 adapter account-write audit (2026-10-20)

## Scope and decision

Audited source: `a0b0aebb874dca71170d80574e4fde6a1a0441a1`, branch
`codex/cx-adapter-audit-20261020`. The frozen production source is unchanged.
This is the source-map discharge requested by the lead-note addendum
“R15 preparation; the account write is an audit item”, beside runtime premise
P2. It is not an AccountInfo extraction or a complete R15 proof.

## Admitted-route write map

Paths below abbreviate `programs/r1-cost-probe/src/` as `P/` and
`crates/aspis-r1-cost-probe/src/` as `C/`. Line numbers refer to the audited
revision; only the separate test file changes in this job. Release features:
`pool-adapter,private-leaf-salts` (no CU observer).

| Stop / write | Guards before the write | Bytes and provenance |
| --- | --- | --- |
| Release dispatch, `P/lib.rs:56–64`, `P/pool_route.rs:3–5` | Before touching accounts: only exact `[3,10]`, `[3,11]`, or `ASQ8` prefix is admitted. Adapter dispatch `P/r1_pool_adapter.rs:1037–1042` selects stage1 or stage2. | No write. Legacy and lifecycle routes cannot bypass this guard. |
| Stage1 inputs, `P/r1_pool_adapter.rs:946–980` | Exact instruction and three accounts at :947; all three keys distinct at :953 (pairwise loop :224–233); proof/public non-signer, non-writable, non-executable at :954–955, :191–204, with arbitrary owners. Checkpoint must have owner equal to `program_id`, be writable, non-signer, non-executable, and have exactly `checkpoint_size(S2)` bytes at :956, :210–221. Mutable borrow :957 is not a write. Every byte must be zero at :958–960. | No write until all later verification succeeds. Original public bytes are borrowed at :961, decoded/validated at :962–964. Candidate prefix must equal the statement's encoded afterstate, total proof buffer length must match, and proof tag must be S2 at :965–980. |
| **Only admitted account write**, `P/r1_pool_adapter.rs:985` | All preceding guards; `first_decoded` must return success at :981; returned-vector length must equal the already exact-sized account at :982–984. | Copies **the entire returned checkpoint vector** into account index 2. Source: `P/lib.rs:49–50` → `verifier::tx1`; compact re-export `C/verifier.rs:515–517` → `C/candidate.rs:270–290`; split exactly 10 (:271), full shape/canonical scan, preparation, batch-A multiproofs, ten queries, finalized pending weights, then `checkpoint(&p,&a,proof,public_bytes,hash)` (:288). Source byte layout below. No payload supplied as arbitrary checkpoint bytes. |
| Stage2 entry, `P/r1_pool_adapter.rs:995–1028` | Seven accounts and ASQ8 magic at :996; exact request length/profile/release/Pool binding :891–900; full authentication :905–911. Checkpoint index 6 is verifier-owned, **read-only**, exact-sized, non-signer/non-executable (:689 and :210–221); all seven keys distinct (:693–701). | **No account writes.** Immutable proof/checkpoint borrows at :1007–1008; public bytes come from re-encoding the authenticated reconstructed statement (:1015–1019); `tx2_authenticated` consumes immutable slices (:1020–1027). No consumed flag or checksum update on this route. |
| Stage2 return buffer, `P/r1_pool_adapter.rs:1000`, :941 | Empty return data is set after route shape checks but before authentication. Successful result is validated against the statement at :932–933, encoded and length/magic checked at :934–939. | `set_return_data(&[])` then, only on success, encoded `PoolV1PairForestTerminalResultV1` at :923–941. This is Solana return data, **not account data**. Result contains kind, master, lane address/id, nullifier and candidate afterstate (:924–930). |

Stage2 authenticates the Pool master, historical Pool checkpoint and selected
lane as read-only Pool-owned accounts at `P/r1_pool_adapter.rs:690–692`;
their decoded identities and PDA addresses are checked at :703–758. Registry
and release-entry accounts are read-only registry-owned at :546, :581/:641,
with policy, PDA, active-release and immutability checks at :535–667. The
historical **Pool checkpoint** (index 2) differs from the **verifier
checkpoint** (index 6). Proof index 0 is a raw read-only buffer at :688.
No AccountInfo enters the core verifier; only immutable data slices do.

**Stage1 conclusion:** on `[3,10]` acceptance the sole account mutation is
replacement of exactly 1,768 initially zero bytes in the distinct verifier-owned
checkpoint. Proof/public data, all account metadata and lamports are untouched.
Every error before :985 leaves account data untouched even in the native model;
there is no fallible release operation after the copy. `[3,11]` is admitted by
the surface guard but rejected by the compact verifier's `k != SPLIT` check,
before account writing (`C/candidate.rs:271–273`).

**Stage2 conclusion:** the verifier neither mutates nor closes any account.
The Pool caller's later settlement writes are outside these two audited files;
the return-data handoff does not itself settle or mark the checkpoint consumed.

### Exhaustiveness against other textual write sites

`P/lib.rs:77` (legacy checkpoint copy) and :80 (consumed-byte and checksum
writes) exist only inside `cfg(not(feature="pool-adapter"))` at :67–89, so
are not compiled into the admitted configuration. They cannot be reached
through `[3,10]` or ASQ8. The lifecycle copies/fill are enumerated below.
All other mutable assignments in the adapter construct local decoded objects,
arrays or vectors; none reference account storage. There is no lamport mutable
borrow, account assignment, reallocation, CPI invocation or account close in
either production file. Test-only AccountInfo setup is not a production write.

## Lifecycle and close authority

**Finding: nobody can close a verifier checkpoint through this release.**
There is no close instruction or lamport-transfer/refund implementation in
these files. In particular tag 6 means **finalize/seal**, not close. The
checkpoint's 1,768-byte raw format has no uploader authority field; ownership
and the release surface protect its contents. Its rent remains locked by this
implementation; a future refund/close instruction would need a separate
authority design and audit. This job sends no transactions and creates or
deletes no wallet/account keys.

For completeness the unreachable helpers have the following complete write
inventory (all in `P/r1_pool_adapter.rs`):

| Tag / write site | Preceding authority and data guards | Effect |
| --- | --- | --- |
| 4, init :361 | :348–360: exactly two instruction bytes, kind 0/1; `lifecycle_accounts` :247–270 requires two distinct keys, target verifier-owned/writable/non-signer/non-executable, authority read-only/**signer**/non-executable/nonzero. Target must have exact header+body length and be entirely zero. | `[0..4]` gets ASPU proof magic or ASRU public magic from the kind. |
| 4, init :362 | Same guards, body length fits u32 (:354–356). | `[4..8]` gets body length in little-endian. |
| 4, init :363 | Same guards. No previous authority is stored in an all-zero account. | `[8..40]` gets the supplied signer's public key. If this helper were exposed, **any** such signer could claim a blank verifier-owned lifecycle buffer; no creator/payer binding exists. It is not an admitted checkpoint writer. |
| 5, upload :400 | Tag/length :373–375; common metadata/signature guards :376; header :383–386, :274–305 requires valid magic, exact encoded/actual body sizes, and stored nonzero `[8..40]` **equal to signer key** (:295–303). Checked offset+payload length and writable-prefix/body bounds :387–399. | Copies caller instruction payload `[5..]` to target `[40+offset .. 40+offset+payload.len()]`. Proof prefix excludes the reserved 1,768-byte tail (:130–145); no header/authority/tail overwrite. |
| 6, finalize :424 | Exact `[6]` :410; common signature guards :413; **stored authority equality with signer** through `validate_lifecycle_header(..., false)` :416; final-body checks :417, :309–339; magic recheck :421–423. | Zeros only `[8..40]`, irreversibly sealing the lifecycle buffer. Proof variant/shape, canonical afterstate and zero reserved tail are checked; public body must decode and validate. No lamports, allocation or owner change. |

The `sealed=true` branch of header validation (:297–298) is **not** used by
upload/finalize; neither accepts a sealed authority field. Thus a different
signer cannot upload/seal another signer's initialized lifecycle buffer even
if the helpers were called directly. A signer is checked by flags furnished
by the runtime, not by host cryptographic signature verification.

**Lifecycle conclusion:** release rejection at `P/lib.rs:61–62` happens
before helper dispatch (:1038–1040), independently of signer identity.
Even internal direct calls cannot finalize a raw verifier checkpoint: its
magic/header/size do not describe an ASPU/ASRU lifecycle account. There is no
“anyone closes someone else's checkpoint” griefing path in this release.
There is a distinct availability caveat: stage1 has no payer/signature
authorization and any caller may initialize a still-zero verifier checkpoint
with a valid proof, if they can submit that account writable. This is the
explicit “anyone can provision” policy, not proof of reservation to its creator;
clients must not treat a published blank address as exclusive. Once nonzero,
stage1 cannot replace it and stage2 cannot alter it.

## Writer proof boundary

The bytes copied at :985 are produced by the **frozen** serializer
`C/verifier.rs:326–340`. Its unkeyed checksum is an integrity check, not an
authorization mechanism. At S2 the exact layout is:

| Checkpoint byte range | Source in frozen writer |
| --- | --- |
| 0..16 | `R1P2CKP2`, variant tag, accumulator `next` (10), status 1, five zero reserve bytes (:328). |
| 16..48; 48..80 | `SolanaDigest` of the compact proof slice; digest of the original public-account bytes (:329; backend `P/lib.rs:10–15`). The candidate-afterstate prefix is excluded from the proof slice at adapter :981; its equality to the public statement was already checked at :976. |
| 80..112; 112..176 | Prepared transcript state and two roots (:329–330). |
| 176..304; 304..320 | Prepared gamma, kappa and two alphas, each 32-byte E; rho, 16-byte K (:331–332, serializers :324–325). |
| 320..408; 408..568; 568..632 | 22 little-endian u32 query indices; ten 16-byte semantic alphas; two circle points, each two 16-byte coordinates (:333–335). |
| 632..696; 696..712; 712..1736 | Prepared claim and accumulated rhs (32-byte E each); accumulated power (16-byte K); 64 accumulated weights (16-byte K each) (:336–338). |
| 1736..1768 | Digest of `[b"UNPROVED:R1:checkpoint", preceding bytes]` (:339). Final length assertion :340; size formula :18, :32. |

This layout is a **source audit**, not an unconditional extracted preservation
theorem. Frozen `resume` checks size/header and recomputes proof, public and
checksum digests (`C/verifier.rs:393–396`). Changes between transactions
therefore reject except for the named hash-collision allowance; ownership,
initial zeroing and exclusive admitted writers still require runtime P2.

The following already checked facts are **on parked branch
`codex/cx-freeze-prep-20261020` at `92e30def94f94b0e400cbd96fba4a94fe485fd48`**,
read with `git show`; their directories are not present at this audit's base.
All paths here are relative to `docs/research/100bit-spend-path-20261013/`.
They are not adopted facts about the frozen serializer:

| Parked fact | Exact evidence and limit |
| --- | --- |
| `AspisR1Tx1Finish.checkpoint_success_length` | `lean/FreezePrepCheckpointLength.lean:18`; `evidence/freeze-prep-20261020/proofs/checkpoint-length-v1/{source.lean,receipt.json}`. Successful complete emitted writer has emitted `checkpoint_size`, parameterized over typed helper operations. `FreezePrepCheckpointBody` retains the emitted writer; no AccountInfo write is included. |
| `AspisR1Stage2.checkpoint_reachable_determinism` | `evidence/tx1-finish-prep-20261020/proofs/checkpoint-facts-01/source.lean:15` and adjacent receipt. Same successful preparation from same bytes, same accumulator/backend/operations ⇒ same writer output. Identifying that preparation with deployed preparation is still owed. |
| `AspisR1Stage2.checkpoint_writer_proof_digest` | Same source :29. Successful writer makes the singleton compact-proof digest call; this alone does not prove that a helper preserves those bytes. |
| `AspisR1Stage2.successful_writer_resume_share_proof_digest` | Same source :51. Under writer **and resume success**, same functional backend, and comparison-soundness premise, stored 16..48 equals the proof digest. This is not unconditional writer preservation, total resume, or a public-digest preservation theorem. |

The earlier writer-length fact is also retained under
`evidence/tx1-finish-prep-20261020/proofs/checkpoint-length-01/` on that
parked branch. These receipts report exit zero and standard axioms only.
`evidence/freeze-prep-20261020/FREEZE-CANDIDATE.md` explicitly parks the
serializer-loop refactor and records the next-freeze adoption obligations.
The adapter and entrypoint are unchanged there, but its core serializer is
different; this audit does not merge it or transport its theorems silently.

Pinned Aeneas failures for AccountInfo slice indexing and the slice-pattern
alternative are retained on that branch under
`evidence/tx1-finish-prep-20261020/receipts/extract-adapter-stage1-10-aeneas/`
and `extract-adapter-pattern-12-aeneas/` (layout attempt 11 is also retained).
Per the lead ruling, the write map above plus P2 replaces extraction of this
account shell. R15 remains open for unconditional writer-field/digest
preservation, helper/backend correspondence, reachable state and the complete
cross-transaction source/model composition. No new Lean theorem or replay is
needed to state the audited account-write result.

## Executable checks and receipts

Packet: `evidence/r15-adapter-write-audit-20261020/` beside this design.
The optimized host command is retained as `run-host.sh`; the host workspace
is `/home/dombarker/project-offloads/codex-cx-adapter-audit-20261020/`.
It contains an independent source/cache copy; no shared build workspace was
rewritten. `input-hashes.json` and `source-validation.json` verify all 228
selected dependency sources/manifests and both saved input buffers byte for
byte against this worktree. The test-only addition is the sole changed entry
in the freeze's 58-file inventory; all 57 other pins match. No production
verifier/adapter source or artifact is changed or rebuilt for SBF.

```
cargo test --release --offline --locked -j 4 \
  -p aspis-r1-cost-probe-program --features pool-adapter,private-leaf-salts \
  --lib -- --test-threads=1
```

| Check | Result |
| --- | --- |
| Added `r15_release_stage1_rejects_occupied_and_wrong_size_without_writes` | Release `[3,10]`: nonzero last byte rejects with AccountAlreadyInitialized; lengths 0/1767/1769 reject with InvalidAccountData. All three accounts' bytes and lamports unchanged. |
| Added `r15_lifecycle_requires_recorded_signer_to_upload_or_seal` | Direct internal upload/finalize: correct key without signature and different signed key both reject without mutation. Recorded signer can seal a valid public buffer; only authority bytes are zeroed; body/lamports remain; repeat sealing rejects. This supplies a positive control, not a fabricated close endpoint. |
| Added `r15_release_rejects_lifecycle_close_attempts_on_real_checkpoint_shape` | Verifier-owned writable raw checkpoint plus stranger signer: init kinds 0/1, upload and `[6]` reject at the entrypoint with InvalidInstructionData; both accounts' data/lamports unchanged. |
| Existing account/provenance teeth | Accepted stage1 writes only checkpoint; repeated stage1 rejects; occupied offsets 0/80/1767; wrong-size/owner/flags/aliases; stage2 read-only exact-size/owner guard and all 21 aliases; proof/public mutation rehash checks; unkeyed-checksum provenance counterexample; release pre-borrow route rejection. All pass. |
| Whole focused program library | **37 passed, 0 failed, 0 ignored**, test runtime 0.01 s. Build+test exit **0**, wall **19.147 s**, peak RSS **561,644 KiB**, swaps **0**. Exact receipt, compiler versions, stdout/stderr and `/usr/bin/time -v` retained. |

The successful scope used `MemoryHigh=6G`, `MemoryMax=8G`,
`MemorySwapMax=0`, `TasksMax=64`, four Cargo jobs and a four-thread linker.
The reservation snapshot found zero populated bounded build scopes, below
55 GiB including this job. Receipt includes actual cgroup memory peak and
limits. Time was expected in incremental compilation followed by account
tests; no dense elimination, proof generation or new fixture generation ran.

The first attempt exited **127** in 0.001 s before compiling: the remote
noninteractive PATH lacked Cargo. Its separate receipt remains under
`receipts/program-lib/`. The replacement launcher explicitly exports
`/home/dombarker/.cargo/bin` and uses a new receipt directory
`receipts/program-lib-path-fixed/`; no unchanged regression was repeated.
The command's source revision is the base above plus the hashed test delta.

These native tests model AccountInfo owner/signature/writable metadata; they
do not prove runtime enforcement, System Program creation, historical zeroing,
validator semantics, or cryptographic signatures. Existing frozen runtime/SBF
evidence is inherited, not replayed here. No Lean work was performed;
`#print axioms` is N/A for this packet. Validate without rerunning tests:

```
python3 docs/research/100bit-spend-path-20261013/evidence/r15-adapter-write-audit-20261020/packet.py --check
```

## Account-read extension (2026-10-20)

The companion [R15 account-read audit](R15-ADAPTER-READ-AUDIT-20261020.md)
extends this map for release `[3,10]` and ASQ8 stage 2: every account data
read, preceding owner/flag/length/distinctness guards, exact core input slices,
and the reconstructed stage-2 public encoding. It distinguishes inherited
stage-2 digest facts from parked, unadopted writer facts and states the
remaining P2/same-byte runtime premise. New focused receipts and test delta
are under `evidence/r15-adapter-read-audit-20261020/`; the original write-audit
packet and its source/doc hashes remain historical evidence for its own revision.
