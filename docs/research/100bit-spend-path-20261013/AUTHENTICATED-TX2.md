# G_R1.3 — authenticated tx2 parser coverage

This is a conditional source-level covering argument and a Rust test report for the frozen v3b parser. It makes no protocol soundness, privacy, deployment, or formal source-semantics claim.

## The covering argument

Let P be the exact proof bytes, X the exact encoded public statement and C the checkpoint emitted after successful tx1. For an authentic C and unchanged P/X, every proof canonicality check omitted by `tx2_authenticated` has already succeeded in tx1. The omitted predicates depend only on those bytes. Rechecking the same predicates would therefore succeed, and strict/authenticated tx2 use the same decoded values in `resume`, query processing and `finish_relation`.

When byte identity is enforced using SHA-256 rather than an exact retained byte comparison, that reasoning is conditional on the digest binding and on checkpoint provenance. The checkpoint checksum is **unkeyed**; it does not establish that tx1 created the checkpoint. Both strict and authenticated tx2 depend on that provenance because neither repeats tx1's semantic verification or its accumulated queries. This note does not turn an arbitrary attacker-supplied checkpoint into authenticated state.

Tx1 calls `View::parse` over the **entire** proof, canonically scanning all 22 initial/folded opening records, including those processed arithmetically only by tx2. It verifies the semantic prefix through `Prefix`, validates its framing/subfield values and ordered transcript, derives prepared challenges and checks its first ten queries. Only successful completion produces C. The checkpoint stores SHA256(P), SHA256(X), transcript state, roots, challenges, query indices, claim, next-query counter, accumulated rhs/power and the final weight vector. Its final checksum covers every preceding checkpoint byte under the checkpoint domain.

Tx2 first performs bounded shape parsing, then `resume`: exact checkpoint size/header/status/reserved bytes/counter, proof/public digests, checksum, canonical checkpoint field values, query range/distinctness and exact reader end. It then processes the remaining queries and relation. The only decoded proof scalar before digest validation is `inactive`, whose canonical check is retained. Unchecked query/round field arithmetic follows `resume`.

## Every named check and its actual location

The request groups several checks as removed from tx2. In the pinned source, only the repeated proof-field scan differs between strict and authenticated tx2. The table distinguishes that optimization from checks retained in both paths and checks performed exclusively by tx1 even before this optimization.

| Check/region | What tx1 establishes | What strict tx2 does | What authenticated tx2 does / covering condition |
| --- | --- | --- | --- |
| Proof magic, variant, reserved bytes, total length | `parse_shape` checks fixed S2 layout and exact length. | Repeats shape checks. | Repeats the same checks; not removed. |
| Semantic record tags and lengths (27 rows) | `Prefix`/`parse_record` check expected tag, exact payload and encoded length; fixed boundaries exclude partial records. | Does not parse semantic records again; digest-bound checkpoint carries derived state. | Same as strict. These checks were not removed by the authenticated-parser change. Changed framing must fail tx1 or checkpoint proof identity. |
| Semantic WideExact canonicality and QM31 restriction | Every value in rows 14–26 is canonical and its high QM31 component is zero. | Does not repeat semantic-prefix validation. | Same as strict; entire prefix is inside SHA256(P). |
| Row order | Prefix consumes the fixed positional schedule; transcript/semantic boundaries bind ordered records, including same-tag round records. | Uses tx1 state, not a second semantic transcript. | Same as strict. There is no explicit serialized row-id in every record. Swapping identical empty records is not a byte mutation. |
| 29 y1 values | Canonical WideExact and zero high component. | Repeats full check. | Skips repeat; tx1 scanned these exact bytes and `resume` checks proof identity. |
| Inactive scalar | Canonical WideExact. | Repeats. | Repeats during shape parse; not removed. |
| Seven round0, seven round1, 64 final values | Canonical WideExact, all eight M31 limbs. | Repeats full check. | Skips repeat; same bytes subsequently feed relation/pairing arithmetic. |
| All 22 × 4 initial openings | Each slot's 26 M31, one QM31 D and two QM31 H1/G values are canonical. | Repeats full scan. | Skips repeat; tx1 includes the twelve queries deferred to tx2. |
| All 22 × 4 folded values | Canonical WideExact. | Repeats full check. | Skips repeat, covered by tx1 and proof identity. |
| Merkle roots/paths | Fixed-length opaque digest bytes; verified where their queries are processed. | Fixed slicing and query authentication. | Same. They have no field-canonicality predicate to omit. |
| Trailing bytes / truncation | Exact full-proof size and semantic-prefix consumption. | Exact proof size. | Same exact proof size; not removed. Full-proof digest does not silently exclude any tail. |
| Checkpoint header / trailing bytes | Tx1 constructs the fixed canonical encoding. | `resume` repeats all header, length, checksum and decoding checks. | Same `resume`; none removed. |

`echeck` consumes 32-byte chunks only on slices whose sizes are fixed multiples of 32. Query widths are computed from the validated variant, not an untrusted record count. The digest covers header, semantic prefix, relation polynomials, final values, every opening and every path. It excludes the outer ASPU header/candidate/checkpoint tail; adapter checks cover that envelope separately.

## Adapter assumptions and writers

For the tested v3b lifecycle, initialization requires a zeroed, exactly sized program-owned account and records a signer upload authority. Writes require that authority and are restricted to the proof/public body before the checkpoint tail, including checked straddle bounds. Finalization requires a zero tail and valid framing/candidate or public encoding, then clears the authority. Stage1 accepts sealed proof/public accounts, checks candidate/public consistency and the zero tail, and writes only its generated checkpoint after strict tx1 succeeds.

Stage2 requires the verifier-owned proof account with read-only, non-executable privileges; reconstructs X from the authenticated account/request path; retains the proof data borrow during verification; and makes no CPI that writes that proof. The proof/public binding therefore concerns the reconstructed current statement, not a caller-selected public digest. Legacy measurement writers operate on an exactly checkpoint-sized separate account and cannot target an embedded ASPU tail. The reviewed lifecycle has no arbitrary header/tail writer or authority reset.

These are assumptions about the account's **entire writable history** under the audited code and the runtime ownership/locking rules. Current program immutability alone does not establish how old program-owned accounts were created. Fresh audited genesis or a separately reviewed migration/provenance mechanism is needed to apply this argument beyond the local fixture. No such deployment assertion is made here. Replay handling is Pool nullifier consumption; authenticated tx2 does not mark the read-only checkpoint consumed.

## Targeted corpus and positive controls

[gr1/native_gate.rs](gr1/native_gate.rs) was compiled in release mode against the frozen v3b archive. For each transfer and withdrawal it generates the complete random-mask proof from the recorded seed, runs tx1, and checks strict/authenticated tx2 acceptance and exact sorted trace equality (9,253 entries). The combined tx1+tx2 trace equals the independently evaluated dense trace (10,699 entries). The corpus then retains that **unchanged valid tx1 checkpoint**, mutates P/X/C, and invokes both entrypoints. Every rejection occurred before a trace-producing arithmetic step in both paths.

| Corpus region | Cases per operation | Result in both tx2 entrypoints |
| --- | ---: | --- |
| Every semantic value: noncanonical low limb / forbidden high component | 426 + 426 | Reject (checkpoint proof binding; tx1 also rejects) |
| Every semantic row tag / encoded length | 27 + 27 | Reject (checkpoint proof binding; tx1 also rejects) |
| Adjacent same-size round-record swaps, rows 15–24 | 9 | Reject; tx1 also rejects |
| y1 canonicality / subfield restriction | 29 + 29 | Reject |
| Inactive scalar | 1 | Reject via retained parse check |
| Every limb of both seven-coefficient rounds | 56 + 56 | Reject |
| Every limb of all 64 final values | 512 | Reject |
| All initial opening M31 slots | 2,288 | Reject |
| All initial D / H1-G limbs | 352 + 704 | Reject |
| Every folded opening WideExact limb | 704 | Reject |
| Proof header and trailing/truncated proof | 4 + 2 | Reject via retained shape checks |
| Each checkpoint header byte, with checksum recomputed | 16 | Reject via retained header checks |
| Checkpoint trailing/truncated bytes and digest/checksum mutations | 2 + 4 | Reject |
| Public-byte mutation | 1 | Reject |
| **Total** | **5,675** | **5,675/5,675 strict; 5,675/5,675 authenticated** |

Exact labels, offsets implied by the generator, mutated input hashes, error variants and trace counts are in [transfer-mutations.json](../../../results/gr1-cost-20261013/full-random/transfer-mutations.json) and [withdrawal-mutations.json](../../../results/gr1-cost-20261013/full-random/withdrawal-mutations.json). For skipped nonsemantic field scans, strict tx2 returns `Parse`, while authenticated tx2 returns `Checkpoint`; equal rejection does not mean identical error classification. Mutations of semantic framing are rejected by both at checkpoint binding, because neither tx2 path reparses the semantic prefix.

The recomputed-checksum header cases specifically exercise checks retained independently of checksum integrity. The corpus does **not** forge a new proof digest/checksum to manufacture arbitrary checkpoint state; such state violates the authentic-tx1 premise and the tested lifecycle boundary.

Each of the five transfer runs for v2 and v3b also executes the nine lifecycle negative cases: tail injection, tail straddle, wrong authority, repeated init, post-seal write, repeated finalize, malformed candidate, malformed public and unsealed stage1. All rejected with byte-preserving rollback. The withdrawal driver omits this repeated lifecycle corpus; its five positive runs compare simulation/execution and expected settlement/custody account bytes. These runtime fixtures support the writer inventory, without replacing its provenance premise.

## Receipts

[Native receipt](../../../results/gr1-cost-20261013/native-full-random-r2.json): exit 0, 42.04 seconds including compilation/proof generation/corpus, sampled aggregate peak RSS 1,041,620,992 bytes, cgroup peak 763,277,312 bytes, swap 0; MemoryHigh 4 GiB, MemoryMax 6 GiB, MemorySwapMax 0. The first attempt failed before compilation because the selected source archive omits unrelated workspace members; their manifest/source files were copied into the isolated workspace without changing any archive member, then the corrected command ran once. Both attempts and repair hashes are retained.

The [source manifest](../../../results/gr1-cost-20261013/native-source-manifest.json), [native results](../../../results/gr1-cost-20261013/full-random/native-gate.json) and [evidence audit](../../../results/gr1-cost-20261013/evidence-audit.json) pin source, inputs, commands and resources. Measured adapter ELF hashes are in [RECONCILIATION-P2.md](RECONCILIATION-P2.md). This corpus is finite executable evidence, not a proof covering arbitrary Rust executions or a closure of G_R1's security obligations.
