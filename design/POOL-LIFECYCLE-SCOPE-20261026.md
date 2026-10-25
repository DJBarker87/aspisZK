# Pool checkpoint lifecycle scope — 26 October 2026

Decision support only. **Recommend option B: prove the checkpoint write/retention
slice plus exhaustive dispatch noninterference, not the entire Pool arithmetic.**
No ledger row is removed, no trust item is adopted, and the deployed soundness
target is not yet established. No concrete accepted attacker-chosen checkpoint
write was found in this source review. This is not a universal verified lifecycle.

## Frozen implementation and account names

`121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` is an
**ELF SHA-256**, not a Git revision. The exact Pool crate is `aspis-pool`,
`programs/aspis-pool/Cargo.toml:1`, entrypoint macro
`programs/aspis-pool/src/processor.rs:130`, dispatch function `:2412`.
The inherited reproducible build used features
`r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit`;
transitive enabled features include account-evidence and verifier-lane-invariant,
but NOT full-ASF8, pair-afterstate, direct-result or deposit-invariant.
See `evidence/lowering2-20261026/Low2_build-pool-v1_command.json` and its
artifact/receipt. The local compiler-input SHA checks match **all 133 Pool inputs**
and all 132 inputs of each verifier variant in that manifest; see
`evidence/pool-scope-20261026/PoolS_inherited-build-match.json`. This reuses the
historical build receipt; it is not a new build, deployed-code attestation or
source-to-SBF refinement. Source anchor: `9c994f068cd3881f05fdf75288a6152286e6c490`.

| Object | Actual role and storage |
|---|---|
| ASQ8 | Terminal **instruction**, 320-byte body (Pool adds four bump hints); never the stored account discriminator. |
| ASC8 | Pool-owned immutable forest checkpoint, **192 bytes**, magic ASC8/version 2, byte 7 stored bump; eight lane sequences and global root. `crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs:34`, `:390`, `:426`. Pool terminal account index 1; verifier CPI index 2. |
| ASF8 | **1,880-byte statement** reconstructed/encoded in memory; TX1 public buffer contains it. Not a Pool checkpoint account, and no standalone ASF8 write instruction is enabled in this Pool ELF. |
| CP | Verifier-owned **1,768-byte** `R1P2CKP2` image, marker byte 0 = 82, state byte 10 = 1; TX1 account index 2 and verifier TX2/CPI index 6. No PDA or authority signer requirement. `crates/aspis-r1-cost-probe/src/verifier.rs:32`, `:326`, `:394`. |

The verifier is a separate crate, `aspis-r1-cost-probe-program`, entrypoint
`programs/r1-cost-probe/src/lib.rs:56`. Its release `pool-adapter` dispatch uses
`r1_pool_adapter_owned.rs`, not the historical borrowed/original bodies.
Abbreviations below: **P** = `programs/aspis-pool/src/processor.rs`, **F** =
`programs/aspis-pool/src/pair_forest.rs`, **D** =
`programs/aspis-pool/src/pair_forest_dispatch.rs`, **O** =
`programs/r1-cost-probe/src/r1_pool_adapter_owned.rs`, **A** =
`programs/r1-cost-probe/src/r1_pool_adapter.rs`. All references are to the pinned,
unchanged local source. The scan receipt lists every mutable-account/CPI site
and its source line, including feature-off and test-only sites for classification.

## Exhaustive entrypoint and mutation inventory

Each row includes its adversarial review. “No” means no path found by inspection
under the named runtime/initial-state conditions, not a checked theorem. Attackers
may choose instruction bytes, account lists and schedules, own proof/public
buffers, pre-fund addresses and invoke programs. Signer status is not a substitute
for ownership. Committed means whole transaction success, not an inner `Ok`.

| ID | Instruction / path and effects | Required guards and alternate-role exclusion | Accepted attacker-chosen checkpoint bytes? |
|---|---|---|---|
| V0 | Verifier release admission: only `[3,10]`, `[3,11]`, or ASQ8 prefix. `lib.rs:56–65`, `pool_route.rs:3–5`, `A:950–965`. | Admission occurs before any account borrow. ASQ8 subsequently needs exact body length and seven accounts. | No extra writer. Malformed prefix rejects. |
| V1 | TX1 `[3,10]` or `[3,11]`: snapshot, run actual verifier TX1, then one full CP copy. `O:376–414`, `:447–460`; `lib.rs:49–51`. **Only reachable verifier account-data write**. | Exactly three distinct keys; proof/public nonsigner, readonly, nonexecutable, arbitrary owners; CP owner = executing verifier, nonsigner, writable, nonexecutable, exactly 1768, all zero. Public decoder + validator; proof exactly 58295, candidate prefix 688 matches encoding, S2 tag; actual first_decoded succeeds, output same length. No PDA or authority signer. | Can choose verifier inputs and a fresh zero account, but output is actual verifier-returned CP, not arbitrary supplied payload. A previously written CP fails zero check. Cryptographic acceptance remains its own obligation. |
| V2 | ASQ8 TX2: snapshots seven accounts; reconstruct ASF8; tx2_authenticated; emit ASR8 return data. `O:230–325`, `:328–372`, `:417–444`, `:463–480`. **No account write, resize, close or assign**. | Distinct seven keys. CP owner executing verifier, length1768, nonsigner, readonly, nonexecutable. Master/lane/ASC8 Pool-owned readonly nonsigners/nonexecutables. Master self-identity/all-lanes plus master PDA; ASC8 master/domain and checkpoint PDA; lane master/id/PDA. Registry/entry owner, versioned PDA, immutable policy, profile/release, programdata/authority and active-slot guards `O:81–226`. Proof canonical prefix/tag/length; request exact320, release/profile/Pool ID; reconstructed statement validation; verifier CP decoder/hash bindings. | No write. Return data is not account storage. Read authentication alone does not establish account provenance or original TX1 byte association. |
| V3 | Loader lifecycle tags 4/init, 5/write, 6/finalize exist at `A:247–427`; legacy tags 1/2 and cost-probe mutation at `lib.rs:68–92`. | All rejected by V0 in selected release. Internal lifecycle additionally requires owner/writable/nonsigner target, distinct nonzero readonly signer authority, proof/public length/discriminator, stored authority/unsealed state and offset bounds. | Unreachable from selected entrypoint. Do not include non-pool-adapter cost probe as an admitted CP writer. Re-evaluate if features/admission change. |
| P0 | Pool dispatch `P:2412–2624`: clears return data, requires transaction-level stack on SBF; no raw append or fallback writer. | Exact selected feature gates and four-byte dispatch; unknown instructions reject. `P:2619` rejects CPI into Pool. Exact account counts and uniqueness are enforced in handlers/layouts. | No write by dispatch itself; return-data clear does not clear CP. |
| P1 | **AS8C**, eight-byte checkpoint instruction: creates/allocates ASC8 if needed, writes full ASC8 and advances master. `F:258–277`, `:744–791`, `:2130–2188`. **Only ASC8 writer**. | Exactly12 unique accounts: master0 writable, lanes1–8 readonly, checkpoint9 writable, payer10, System11. Payer system-owned writable signer/nonexec; System exact native-loader executable readonly nonsigner (`P:211`). Master Pool-owned nonsigner/nonexec, ASM8/v2 exact384, self identity, master PDA. Eight lanes Pool-owned nonsigner/nonexec readonly, ASL8/v2 exact768, lane IDs/order/master/PDA and strict tree codec (`F:430–544`). ASC8 address = PDA `[aspis-pair-forest-checkpoint-v1, master, sequence_le, bump]`, sequence from authenticated master. Pool-owned exact192 all-zero OR System-owned empty; recheck exact192/zero/rent after CPI (`P:273`, `F:400`). Pure planner all-lanes, canonical root, nondecreasing lanes with progress after first, checked sequence increment; encoder ASC8/v2/eight lanes/digest version/domain. `pair_forest_accounts.rs:488–548`. | Permissionless caller can request a checkpoint of **current authenticated state**, not supply its bytes. Existing ASC8 starts 65 and fails zero/freshness. Cannot target CP1768: owner/size guards reject. No signer controls the stored snapshot. |
| P2 | **AS8I** initialize: writes master and eight lane images; creates PDAs and token vault. `F:1994–2126`. | Exactly14 unique accounts; payer/System/token/mint guards. Master seeds `[aspis-pair-forest-master-v1,mint,bump]`, lanes `[aspis-pair-forest-lane-v1,master,lane_id,bump]`; fresh System-empty or Pool-zero; exact384/768 and rent rechecks; token vault separate owner/size. | Neither checkpoint writable role accepts occupied ASC8 or CP. A zero initial account alone does not count as an authenticated checkpoint. No checkpoint close/reset. |
| P3 | **AS8D** deposit: lane + current/genesis/rollover root page writes, System creation if needed, SPL transfer. `F:988–1190`, helpers `:806–986`. | Master readonly ASM8/PDA; commitment-selected lane, capacity, ASL8 strict codec/PDA; exact layout + unique accounts; page PDA `[aspis-pool-root-page-v1,lane,page_number,bump]`, page format/length or zero exact page; payer/System/token/mint/authority and exact token balance delta. Lane768/page8256 images are distinct from ASC8. | No ASC8/CP target accepted as lane/page/token. No arbitrary payload writer. |
| P4 | **ASQ8** transfer/withdrawal: master and ASC8 read; reserve marker with System CPI, verifier CPI, optional SPL withdrawal; lane/page/marker writes. `F:1218–1382`, `:1615–1820`. | Exact request+4 hints; master/ASC8/lane decoders/PDA/domain and source-root relation; unique full account list; payer/System. Marker canonical-nullifier seed, address `create_with_seed(master, packed_hash_seed, Pool)`, zero exact marker/owner/rent recheck (`nullifier.rs:93–119`, `:190–282`; `P:1631`). CP appended after full layout, readonly/nonsigner/nonexec/verifier-owned; distinct from all roles. Master readonly, ASC8 readonly, lane writable. Source/result invariant feature remains explicit. | No checkpoint write. Wrong-role ASC8 rejects format/size/freshness; CP rejects foreign owner. Marker reservation and prior effects roll back on any later failure. |
| P5 | **ASIN** legacy initialize. `P:625–726`; `transition.rs:562–610`. | Exactly7 unique; payer/System/token/mint; canonical state `[aspis-pool-state-v1,mint,bump]` and page0 PDAs; zero exact state/page, rent; token vault exact165 SPL-owned. | No checkpoint alias: fresh zero and type/length guards; no close/reset. |
| P6 | **ASDI** legacy deposit. `P:738–851`; `deposit_transport.rs`, `transition.rs:680–742`. | Canonical Pool state owner/writable/nonsigner/format/PDA; canonical current/rollover page with header/size/zero and history consistency, exact layout and unique accounts; SPL transfer authority and balances. | Cannot decode ASC8 as legacy state/page; no CP owner authority. |
| P7 | **ASPT**, **ASWD** legacy private transfer/withdrawal. `P:2024–2187`, `:2189–2379`; `transition.rs:680–742`; `P:1983–2022`. | Canonical legacy state/page and spend binding, exact unique layout, authenticated readonly verifier/registry/proof path; fresh canonical nullifier marker; withdrawal SPL guards. Writes only state/page/marker; SPL custody CPI. | No ASC8/CP writable role passes owner/type/size/freshness. A proof buffer role is readonly. |
| P8 | **ASPP** prepare settlement. `P:1167–1363`, `:1107–1164`. | Canonical legacy state and page binding, exact unique layout; payer/System; receipt/registry authentication; plan PDA bound to pool/statement-digest/source-sequence/authority under `aspis-settle-plan-v1` (`prepared_settlement_format.rs:223`); optional rollover PDA `[aspis-settle-roll-v1,core_plan,bump]` `:243`; fresh exact10000/8504 zero plans. Writes plans, may create zero rollover page. | Cannot repurpose occupied192 ASC8 or1768 CP as a plan or page. No checkpoint bytes supplied by stored plan. |
| P9 | **ASPX** cancel prepared settlement; closes only plans. `P:1462–1578`. | Exact unique layout; writable System-owned signer plan authority; exact owner/nonexec/nonsigner/writable plan10000 and optional8504; ASPS/ASRS format/digest/PDA/stored authority authorization before close (`prepared_settlement_format.rs:580`, `prepared_settlement.rs` close authorization). | ASC8/CP fail exact size before close. Refund destination signer does not grant authority over other program data. |
| P10 | **ASPF** settle prepared: write legacy state/pages/marker and close plans. `P:1674–1910`. | Canonical state/layout; unique accounts; signer payer/authority; same exact plan gates as P9; receipt authentication, plan source-state/digest/PDA/authority, activation/expiry checks; marker and token guards. | No checkpoint write or close via plan role; length/type/owner exclusions apply before mutations. |
| P11 | **ASJP/ASJW** pair-afterstate; **ASF8** full-statement terminal. Dispatch `P:2484–2502`, `:2547–2583`; bodies `pair_processor.rs:284–586`, `F:1890–1939`. | Feature-off in selected ELF. Full-ASF8 body decodes statement then delegates compact terminal with hints; pair-afterstate writes pair1000/page/marker, never CP. | Unreachable. No feature-off branch is counted as a deployed writer. |
| H1 | Shared fresh-account create/allocate/top-up/assign. `P:273–449`, `:567–623`; `P:513–557` vault initialization. | Callers authenticate expected PDA/seed and exact output type; System owner + empty for allocation/assignment. Zero-lamport CreateAccount or prefunded transfer+Allocate+Assign; correct PDA signer seeds. WithSeed variant uses authenticated master base. Vault assigned SPL owner, not Pool. | May establish **zero** owner-assigned initial state, never inject nonzero CP/ASC8. Already initialized owner-owned checkpoint not System-empty and not all-zero. Size mismatch blocks a fresh Pool checkpoint being used for another type. |
| H2 | Shared close: tombstone0xff, checked refund, zero lamports, System assign, resize0. `P:236–271`, only callers P9/P10. | Owner/writable/nonexec/nonsigner, exact supplied plan10000/8504, distinct writable refund; caller authenticates plan. | No checkpoint close caller. No claim about correctness of unrelated successful plan close is needed: checkpoint rejection precedes tombstone/refund. |
| C1 | Pool→verifier CPI. `D:92–139`, `:178–243`, `:281–398`. | Selected executable/loader and registry policy/profile/release/slot binding; proof/master/ASC8/lane/registry/entry/CP are **all readonly nonsigner CPI metas**; CP owner selected verifier and distinct. Clear/invoke/get return data; returned program/length/ASR8 decode. | Callee owner can write its own data only when writable; CP is readonly. Pool cannot grant a write via this CPI. No CPI from verifier's active TX1/TX2 bodies. |
| C2 | Pool→System and Pool→legacy SPL Token. `P:321–449`, `:513–557`; `F:1100–1172`, `:1690–1794`; vault exact-info builders. | Fixed executable IDs; authenticated payer/PDA seeds and token owners/mint/authority; checkpoint cannot pass token/account role guards; no forwarded writable verifier checkpoint. | Other owners cannot write either retained checkpoint. Lamport credits alone are allowed and change no checkpoint bytes. |
| R1 | External System CreateAccount/Allocate/Assign, including attacker-owned keys or another program assigning its account to verifier/Pool. | Runtime ownership/zero-data assignment and signer rules. A keypair may create a zero1768 verifier-owned account; CP deliberately need not be a PDA. A foreign program assigning to Pool/verifier must relinquish **zero** bytes. Pool PDA creation additionally needs Pool signing. | Produces zero genesis only. No nonzero attacker bytes may accompany assignment. Proving this admission is required; merely assuming arbitrary initial owner/data would make writer-origin false. |
| R2 | External writes/resize/assign/close or CPI into owning program. | Only current owner modifies/debits/changes length; readonly prevents writes; owner reassignment needs zero data. Another program may call verifier V1 on zero CP (legitimate origin), or V2 readonly; cannot call disabled loaders. CPI into Pool rejected by stack guard. | No foreign direct write. Owning-program CPI is already classified by V0–V3/P0–P11; privilege escalation cannot bypass runtime flags. |
| R3 | Error, panic, borrow/allocation failure, failed CPI, later transaction failure; fork rollback. | Failed transaction effects are discarded atomically. In an enclosing program that catches a failed CPI, failed child effects must still be restored by runtime. Only canonical committed history is used. | Transient writes are not origins. A rolled-back TX1 cannot explain a later nonzero committed CP; a rolled-back competing write cannot replace bytes. Fork history must not splice a writer from another bank. |
| R4 | Loader upgrade/redeployment, validator/genesis injection or arbitrary initial snapshot. | Outside fixed-ELF semantics. Registry immutability checks do not alone attest actual loader deployment state; deployment/programdata/authority pins must be supplied. | Could invalidate exhaustive dispatch/genesis if admitted. Explicit release/runtime boundary, not silently a new assumption or a discovered source attack. |

There is no shipped production `unsafe` block in the Pool crate prefixes scanned;
SDK/runtime entrypoint memory handling is outside that statement. Test mocks
that assign/resize or mutate accounts (`F` after2224, `prepared_settlement.rs`
after its test module, vault test writer) are not executable instructions.
The verifier's non-pool-adapter unsafe heap diagnostic is feature-excluded.
Neither a signature nor PDA seed protects an account against **its own owner's**
other instructions: the alternate-role/type/size checks above are essential.

## Exact property needed by soundness

Fix the **same canonical committed execution history**, pinned verifier V and
Pool P, runtime/ABI/allocator interpretations and cryptographic children. Admit
initial accounts only through a proved genesis/creation history: first assignment
to V/P supplies zero data, not arbitrary preloaded owner-authenticated bytes.
Freeze programs throughout this interval, or separately prove equivalent upgrades.
Use public keys as account identities, with runtime alias coherence; do not use
independently supplied byte arrays as a substitute for account history.

Let `load(e2,k)` be the actual CP bytes snapshotted by an accepted V2 TX2 at O:477,
subsequently passed at O:439, with owner V, length1768. Then there exists a
**committed accepted V1 invocation e1**, strictly earlier than that load, whose
actual account2 key is k and whose actual verifier-returned bytes c were copied
at O:457, such that:

1. `c = load(e2,k)` as complete bytes, `length(c)=1768`, and the native successful
   TX1 child of e1 produced c on e1's original proof/public inputs.
2. Immediately after e1's committed copy, `store[k].data = c`; at e2's snapshot,
   `store[k].data = c`. Throughout the intervening canonical history there is
   **no committed accepted data write, resize, close/deallocation, or owner
   reassignment of k**. Failed/transient writes restore their prestate. Lamport
   credits are permitted; no stronger unchanged-lamports claim is needed here.
3. The chosen e1 is the actual causal writer of that physical account, not a
   separately existential accepted TX1 with a matching digest. Since c begins
   with82 and V1 requires every prior byte zero, no second accepted V1 can
   overwrite k while its initialized owner/data state persists.

This is a writer-origin and retention theorem, **not** a theorem that TX1 alone
finishes verification, nor an assumption of hash injectivity. TX2 checkpoint
parsing accepts only nonzero magic (`verifier.rs:394`), so a zero newly assigned
account cannot be its successful input. The statement is false if arbitrary
initial nonzero V-owned accounts are admitted without provenance; that is an
initial-state model obstruction, not an exhibited shipped-source attack.

Dependencies for CP: V0/V1 (unique writer, actual output and nonzero marker),
V2 (actual key/snapshot/load, readonly), V3 (unreachable alternate writers),
P0–P11/H1–H2/C1–C2 (Pool cannot write V-owned CP or pass it writable), R1–R4
(genesis, ownership, schedule, rollback and fixed deployment). For CP retention
alone, Pool is a foreign owner and a short runtime argument plus verifier CPI
meta inspection suffices; proving all Pool arithmetic is unnecessary.

The additional **Pool ASC8 origin/retention property** needed for L180 is separate:
any ASC8 account q read by that same V2 was created by a committed accepted P1
AS8C on q's authenticated master/sequence; its complete image is exactly the
planner/encoder output for the eight authenticated lane snapshots of that action,
and no later committed mutation/resize/close/reassignment changes q before the
load. No claim is made that AS8C requires verifier TX1: **it does not**. ASC8 is
created permissionlessly from Pool state. Its provenance depends on P1/H1/R1,
noninterference on every P2–P11/H2/C1–C2/R2–R4, and causal loading on V2/P4.
The stored discriminator ASC8, exact192 length and occupied-byte rejection
provide a short preservation invariant. Source state correctness additionally
needs initialization plus every lane/master writer (P2/P3/P4); an immutable
ASC8 can still be wrong if the upstream source-state invariant is unproved.

P2Prime proof/public equality is another obligation. Proof/public buffers have
arbitrary owners, and readonly flags protect one invocation only. Neither CP
retention nor ASC8 immutability establishes their cross-transaction identity.
Reuse the Hist_/Hiq_/Hir_ measured SAME-world collision/log argument and actual
reconstruction/validator/encoder cuts; keep all rejected-prefix/adversary queries
and byte association. Do not remove L097/L098 using this inventory alone.
No complete scheduler/query-budget transport, L159 or endpoint probability
refinement is claimed. Rows L094–L098 and L180 remain open.

## Proof scope, sizes and decision

Counts below are **source measurements or engineering estimates**, not timings,
proof counts, or an assertion of automated extraction coverage.
`PoolS_surface-scan.json` counts lexical `fn`, loop and unsafe tokens after
comment removal, up to each file's final test module; includes trait signatures,
feature-off functions and some test-only helpers. Consequently gross file totals
are upper envelopes, not the live callgraph. External SDK/crypto bodies are extra.

| Component | Measured source envelope (lines / fn tokens / loop tokens / unsafe tokens) |
|---|---|
| All Pool src files | 14,364 / 402 / 52 / 0; test/feature caveat above. |
| Pool processor | 2,625 / 46 / 3 / 0. |
| Forest accounts/instructions | 2,223 / 62 / 14 / 0. |
| Forest verifier CPI dispatch | 478 / 18 / 2 / 0. |
| Pair processor (feature-off here) | 588 / 6 / 1 / 0. |
| Pure forest account codec/planner | 550 / 13 / 8 / 0. |
| Actual owned verifier adapter | 481 / 17 / 3 / 0. |
| Parent verifier adapter | 973 / 32 / 2 / 0, includes dead lifecycle and borrowed helpers. |

The tight ASC8 write kernel is `F:704–791` (three functions,88 lines),
`F:2130–2188` (one function,59 lines), freshness `F:400–415` (one,16 lines),
`P:273–297` (one,25 lines), pure checkpoint encode/decode `:390–486`
(two,97 lines) and planner `:488–548` (one,61 lines): **nine functions,
346 source-span lines** before callees. Includes fixed8 lane loops, exact192
zero scans, encoder sequences and checked-u64 chronology. Master/lane decoders,
PDA/hash and System-CPI helpers are not included in those346 lines and cannot
be silently omitted. The verifier CP admission/copy core `O:376–414`,
`:447–460`, require-zero `:73–79`, checkpoint metadata `:51–58` is four
functions/68 lines, plus snapshots/alias/child/body cleanup and runtime bridges.
These span counts include blank lines/comments and are review sizing only.

| Option | Scope and estimated additional effort | Reuse and limitation |
|---|---|---|
| A — complete relevant lifecycle by extraction/P6 | All11 live Pool handler kinds (AS8I/C/D, ASQ8, ASIN, ASDI, ASPP/X/F, ASPT, ASWD), dispatcher and dependent helpers; verifier V1/V2 and admission. Roughly180–300 reachable helper/method instances,8–14k local source lines,35–55 loop sites before crypto/SDK dependencies; **6–12 engineer-weeks /60–120 focused targets**, high uncertainty. Gross envelope above prevents claiming an exact extracted callgraph. Includes zero local production unsafe but imported SDK/entrypoint unsafe, syscalls, CPI and rollback. | Reuse native TX1/TX2/copy/SDK children, pure codecs/invariants, history proofs. Full Pool Aeneas extraction has already failed in shared zero check (`pair_forest.rs:400–415`, internal Unreachable at SymbolicToPureValues.ml:878), despite Charon success. Do not rerun unchanged or build new launcher infrastructure. P6 must relate actual code, effects and errors; assuming a full lifecycle law would not prove it. |
| B — write slice plus exhaustive noninterference (**recommended**) | Prove the nine-function ASC8 write kernel, add metadata/decoder/PDA/CPI callees (about20–35 functions,0.9–1.6k lines,8–15 local loop sites); CP unique-writer slice reuses native child proofs. Prove short-circuit occupied-checkpoint exclusion for each other live handler and fixed-owner effects (about25–45 guard/helper instances,1–2k source lines reviewed, overlaps prior count). Runtime genesis/rollback/load association is a separate6–10 targets. Estimate **2–4 engineer-weeks /25–45 focused targets** total, contingent on existing child gates; not a guarantee within this job's20/10 budget. | Reuse Hir_ freshness/planner/encoder/close rejection and reader-owner Kani gates; Hiq_ extracted Pool metadata and whole verifier release dispatcher; Hist_ source marker/same-account retention; Hir_ causal-writer selection, lifetime log, same-world loss; SInt2 actual owned source/copy children. Avoid forest tree/hash normalization for noninterference: a192-byte occupied account fails another writable role before heavy arithmetic. Preserve all earlier effects/errors, prove frames, and bind the runtime instance. A wrapper assuming “only AS8C writes” is insufficient. |
| C — reviewed deployment trust item | Publish precise named fixed-deployment lifecycle/provenance law covering ALL inventory rows, genesis and rollback; independent source/loader review and owner approval. Roughly2–4 reviewer-days plus owner/security-contract decision;0–3 integration targets, **no source-refinement closure credit**. | Existing review/ELF pins support the review only. Route-B SDK trust expressly excludes realloc, lamport borrows, CPI, concurrency/reentrancy; it does not authorize this item. This would enlarge headline trust and require explicit owner/contract adoption. The worker does not adopt it or relabel open rows proved. |

Recommendation B is sufficient **for origin/retention** if the runtime instance
and exhaustive dispatch frames are actually supplied. It is not a shortcut to
all source-state correctness or the deployed soundness probability bound.
Use a targeted P6/accepted-run slice or extraction isolation of the already
failing zero guard; no unchanged failing full-Pool extraction retry. If extraction
cannot support that small slice, report the exact obstruction to the lead before
commissioning another history-only wrapper. Do not silently choose C.

Concrete next deliverable: a `PoolS_` (or newly assigned worker prefix) source
certificate keyed by physical account/public key and canonical committed action,
covering P1's actual post-CPI copy and every other handler's occupied-ASC8 frame;
then instantiate Hir_'s selected-writer/load/genesis obligations on that SAME
history, preserving real verifier child/copy observations and full source log.
Budget that work separately; this scoping job launches no proof campaign.

## Runtime references and assurance boundary

Runtime rules used in R1–R3: current owner and writable privileges govern data
updates/resize/debits, and changing ownership requires zero-initialized data.
These justify why foreign assignment cannot manufacture a nonzero checkpoint;
see [Solana account modification rules](https://solana.com/docs/core/accounts/modification-rules).
Transaction instructions execute atomically and a failed transaction discards
account modifications; see [Solana validator runtime](https://beta.docs.solanalabs.com/validator/runtime).
These current primary documents explain the intended boundary; they do not
certify the pinned validator build or prove the runtime instance. The proof
must use the release's exact runtime/ABI pins, including failed-CPI restoration,
account aliasing and canonical-bank history, rather than substitute these pages
for executable semantics.

## Validation and handoff

No source, feature, dependency, ELF, key or live account changed. Only this
requested design file and `evidence/pool-scope-20261026/PoolS_` receipts changed.
Default/devnet/Pool inherited ELF hashes remain respectively
`f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`,
`63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`,
`121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.
All historical source input hashes match; no rebuild trigger fired.

New Lean invocations **0/20**, Kani runs **0/10**, Rust builds0. No new theorem,
axiom or formal release result; `#print axioms`, formal target/exit/wall/peak
RSS/swap are **not applicable**. Historical Hir_/Hiq_/Hist_ results retain their
own receipts, scope and standard-axiom audits; they were not rerun. No large
job or host reservation was launched. Inspection validation and source pin
comparisons are in the PoolS receipts. No assumption was discharged, retained
assumptions were not strengthened or renamed, no global row was removed, and
no new security trust, metric or target was adopted. Main remaining blocker:
complete deployed runtime/Pool instance of the history/lifecycle property.
