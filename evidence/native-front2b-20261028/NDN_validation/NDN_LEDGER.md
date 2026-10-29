# NDK authoritative native composition ledger

Pinned research head `599016a1629bd0e760dcb506cc9a3417bd0b0a94`; frozen Rust `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. **Deployed 100-bit target not yet established.**

NCZ reconstruction is refreshed with explicit NDD/NDF/NDG decisions and all merged packet reviews. Local conditional credit retains the exact domain, reference/cohort carrier, dictionary selection and physical interpretation. Every composed row remains OPEN; this audit discharges no security or native caller premise.

| Inventory | Conditional before | Conditional after | OPEN before | OPEN after | Quarantined before/after |
|---|---:|---:|---:|---:|---:|
| TX1 | 106 | 124 | 237 | 219 | 2/2 |
| TX2 | 107 | 119 | 133 | 121 | 2/2 |
| all_rows | 213 | 243 | 370 | 340 | 4/4 |
| unique_functions | 120 | 141 | 312 | 291 | 2/2 |

Changed inventory rows: **30**. Composed OPEN: **587/587**, unconditional CLOSED: **0**. Trust-only body credit: **0**.

Recomputed minimum reachability-cover frontier: **133 → 130 SCC representatives**. This graph statistic need not decrease when leaves close. It is neither a runtime critical path nor a sufficient proof set.

## Admitted and rejected frontier deltas

| Function | Decision | Domain / remaining obligation |
|---|---|---|
| `crates/aspis-core/src/field.rs::M31::reduce_u62` | ADMIT LOCAL CONDITIONAL | value < 2^62; Same native/cohort caller carrier and installed dictionary association remain OPEN. Caller domain and physical interpretation remain OPEN. |
| `crates/aspis-core/src/field.rs::PreparedQm31Multiplier::new` | ADMIT LOCAL CONDITIONAL | four canonical u32 limbs; Same native/cohort caller carrier and installed dictionary association remain OPEN. Caller domain and physical interpretation remain OPEN. |
| `crates/aspis-r1-cost-probe/src/weights.rs::field` | REJECT STATUS PROMOTION | No closed native domain; Only the selected-window/unchanged-Some decoder cut is checked. Instantiate the CLOSED real decoder value/success/carrier law on these SAME bytes, prove canonical caller bytes and offsets, and replace the abstract decoder cut with an admissible native callee bridge. Needs Kani; the conditional Lean selector cut is complete. |
| `crates/aspis-core/src/field.rs::CM31::from_m31` | ADMIT LOCAL CONDITIONAL | all u32 inputs; Same native/cohort caller carrier and installed dictionary association remain OPEN. Caller domain and physical interpretation remain OPEN. |
| `crates/aspis-core/src/field.rs::qm31_pack_base4` | REJECT STATUS PROMOTION | No closed native domain; K037/K038 full checks and K067 isolated-limb/verified-reducer shape timed out; K066 was codegen-only. Copy window, four exact raw arithmetic spans and reducer contract are separate checks. Native SAME-execution association from the actual padded buffer to all four spans/returns remains OPEN. The cohort arithmetic cut/reference equality is proved; no whole-buffer retry or cap increase is justified. Needs new split native association, not more arithmetic normalization. |
| `crates/aspis-core/src/field.rs::CM31::square` | REJECT STATUS PROMOTION | No closed native domain; The actual real-coordinate path contains an inline u64 product before reduce_u64. It cannot be verified by multiplying in Kani or by replacing only M31::mul. Need a native raw-factor/product opaque log and association to the already checked symbolic square/product law, with canonical inputs established. Needs Kani; existing mathematical product/word laws are reusable. |
| `crates/aspis-core/src/field/wide_exact.rs::WideExact::square` | REJECT STATUS PROMOTION | No closed native domain; Depends on open CM31 square through QM31::square, plus actual mixed cross-product/coordinate call log and a resolved cohort consumer (no named counterpart in the inventory). Need native call-domain/step association using Lean-discharged multiplication laws. No whole-product Kani run is allowed. |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits` | REJECT STATUS PROMOTION | No closed native domain; Native contract and extracted value specification pass, but the inventory has no named cohort helper. Associate this scalar to the enclosing adopted multiproof arity/shift consumer, including binary versus eight-way domain; needs a native caller/cut association. |
| `crates/aspis-core/src/field.rs::qm31_from_karatsuba_channel_sums` | ADMIT LOCAL CONDITIONAL | all nine u64 channel sums; Same native/cohort caller carrier and installed dictionary association remain OPEN. Caller domain and physical interpretation remain OPEN. |
| `crates/aspis-core/src/field.rs::CM31::neg` | ADMIT LOCAL CONDITIONAL | two words < P; Same native/cohort caller carrier and installed dictionary association remain OPEN. Caller domain and physical interpretation remain OPEN. |
| `crates/aspis-core/src/field.rs::QM31::neg` | REJECT STATUS PROMOTION | No closed native domain; Canonical native contract/control pass. No resolved named cohort counterpart; associate the actual four coordinates to its enclosing model use, rather than creating a stand-in. Needs a native/model caller packet. |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::index_at` | REJECT STATUS PROMOTION | No closed native domain; Native/extracted array indexing is checked for index<16, with total reference Result law. No named adopted helper; prove each actual caller index/domain and match the cohort inlined access. Needs native caller association. |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed` | REJECT STATUS PROMOTION | No closed native domain; One windows predicate/membership step is checked; allM_total proves library induction. Still need actual windows iterator/pre-state association, length/nonempty gates, early rejection and enclosing cohort counterpart. Full-buffer Kani is forbidden. Needs native iteration/caller association. |
| `crates/aspis-core/src/field.rs::qm31_accumulate_product_channels` | REJECT STATUS PROMOTION | No closed native domain; Native nested iteration contains raw u64 products and += on arbitrary sums. Need one arbitrary-pre-state channel iteration with the <=four-products invariant, operand/carry log and a paired emitted natural product law. Multiplication must remain Lean-only. Needs Kani source-step association. |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::occupied_binary_parent` | REJECT STATUS PROMOTION | No closed native domain; Exact tag/left/right slices and arbitrary reply unchanged are checked with a static recorder. No named cohort helper; bind this boundary to the SAME adopted parent/digest operation and prove index+1<16 at every caller. RuntimeSha256Value remains trust. Needs native caller/cohort association. |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::root_matches` | REJECT STATUS PROMOTION | No closed native domain; Native first-root comparison and extracted Result specification pass. No named cohort helper; bind this comparison to the SAME adopted root/value arrays and caller domain. Needs native caller association. |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::sibling_binary_parent` | REJECT STATUS PROMOTION | No closed native domain; Both left/right exact slice order and unchanged reply are checked for a 32-byte sibling and index<16. Associate the actual node range and enclosing cohort digest boundary; no named helper is inventoried. Runtime digest value remains trust. Needs native caller association. |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::value_at` | REJECT STATUS PROMOTION | No closed native domain; Native fixed-array result/control and extracted Result indexing law pass for index<16. No named cohort helper; instantiate the enclosing model access on the SAME array/index. Needs native caller association. |
| `crates/aspis-core/src/field.rs::QM31::is_zero` | ADMIT LOCAL CONDITIONAL | all four u32 words; Same native/cohort caller carrier and installed dictionary association remain OPEN. Caller domain and physical interpretation remain OPEN. |
| `crates/aspis-core/src/field.rs::qm31_m31_dot` | REJECT STATUS PROMOTION | No closed native domain; Both branches contain raw limb u64 products; long branch also has four-product blocks and reduced outer sums. Need one native iteration, product/carry-domain log and Lean induction for each branch, then native/model association. No whole-buffer Kani or direct field multiplication is allowed. Needs Kani. |
| `crates/aspis-core/src/field.rs::M31::neg` | ADMIT LOCAL CONDITIONAL | x < 2147483647; Same native/cohort caller carrier and installed dictionary association remain OPEN. Caller domain and physical interpretation remain OPEN. |
| `crates/aspis-core/src/field/wide_exact.rs::WideExact::neg` | REJECT STATUS PROMOTION | No closed native domain; Canonical eight-limb native contract/control pass. No named cohort counterpart is resolved; bind the two QM31 negations and actual eight-coordinate carrier to the adopted consumer. Needs native/model caller association. |
| `crates/aspis-r1-cost-probe/src/weights.rs::Weights::scalar_factor` | REJECT STATUS PROMOTION | No closed native domain; Need one arbitrary-pre-state fold iteration (s<4), exact PERM selection, canonical E/K accumulators and translated multiplication return log, then final QUARTER scaling association. Existing multiplication value laws may be reused; none is replaced by an unpaired stub here. Needs Kani. |
| `crates/aspis-r1-cost-probe/src/weights.rs::Weights::tensor` | REJECT STATUS PROMOTION | No closed native domain; Need native iteration on arbitrary invariant output state, k<5, folds<=5, n/index/length bounds, reverse-order read-before-overwrite and four multiplication logs; then Lean induction. No complete output buffer may be unwound. Needs Kani. |
| `crates/aspis-r1-cost-probe/src/weights.rs::high_dot` | REJECT STATUS PROMOTION | No closed native domain; Need one actual EbyKDot::push iteration on arbitrary state, canonical operands, Result/error path and SAME raw accumulator carrier, followed by finish association. Raw-dot emitted law and field laws exist; whole four-push execution is not a substitute for the required iteration cut. Needs Kani. |
| `crates/aspis-r1-cost-probe/src/weights.rs::Weights::box_from_parts` | REJECT STATUS PROMOTION | No closed native domain; The model constructor returns a record and erases Box allocation/ownership. Need native arbitrary-field window transport plus allocation/ownership/frame/cleanup interpretation; scalar/fixed-array contract permission does not automatically admit a Box return. The exact model constructor fact is proved. Needs native/allocator evidence. |
| `crates/aspis-r1-cost-probe/src/weights.rs::double` | REJECT STATUS PROMOTION | No closed native domain; Correct QM31 model performs one product, frozen source performs two SAME-input products. Native opaque multiplication observations, deterministic value association and canonical domains remain missing. M31-named overloads are not this function. Checked-to-wrapping recombination and conditional reference/model theorem are proved. Needs Kani. |
| `crates/aspis-r1-cost-probe/src/weights.rs::shared_two_point_guard` | REJECT STATUS PROMOTION | No closed native domain; Native complete-record checks pass. The reference takes Boolean comparison cuts; prove SAME row/variant and derived-array equality carrier association to those exact cohort comparisons (or use a fuller raw-word reference and recheck natively). Conditional model cut is proved; do not treat its comparison hypotheses as discharged. Needs native/model equality association. |
| `crates/aspis-r1-cost-probe/src/candidate.rs::opening` | ADMIT LOCAL CONDITIONAL | proof.len=57607; i<22; readonly byte/slice interpretation; Same native/cohort caller carrier and installed dictionary association remain OPEN. Pointer+length equality, not a borrowed-return substitution contract. Caller selected-index proof uses the existing Port4B opening geometry. |
| `crates/aspis-r1-cost-probe/src/candidate.rs::batch_key_at` | ADMIT LOCAL CONDITIONAL | 16 U64 keys; index<16; Same native/cohort caller carrier and installed dictionary association remain OPEN. Local source getter only; whole sort/batch trace and same-execution caller invariant remain OPEN. |
| `crates/aspis-r1-cost-probe/src/verifier.rs::update_residue_row` | REJECT STATUS PROMOTION | canonical power/basis limbs; group-bound raw residues; Requires one actual native arbitrary-row/limb iteration and opaque product-log association, plus four-cell/frame induction. Raw primitive products are not discharged by the named field-call stubs. Multiplication must not be proved in Kani; no larger/full-row run licensed. |
| `crates/aspis-r1-cost-probe/src/candidate.rs::batch_keys` | REJECT STATUS PROMOTION | lo/n=(0,10) or (10,12); tree0..2; canonical 22 queries; Full producer induction already exists. Missing actual native one-write iteration/source-step association and actual loop trace; do not replace with whole-buffer Kani. |
| `crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_index` | ADMIT LOCAL CONDITIONAL | 16 U32 values; index<16; arbitrary expected; Same native/cohort caller carrier and installed dictionary association remain OPEN. Local source Bool result; same-execution dedup count invariant remains caller-owned. |
| `crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_leaf` | ADMIT LOCAL CONDITIONAL | 16 arrays of 32 bytes; index<16; arbitrary leaf; Same native/cohort caller carrier and installed dictionary association remain OPEN. Exact KMX mitigation retained; no parent duplicate-handling claim. |
| `crates/aspis-r1-cost-probe/src/verifier.rs::mark` | REJECT STATUS PROMOTION | release observer None; Native Option<fn>/function-pointer-dependent evidence is quarantined by rule14. A Lean None identity cannot lift this quarantine. |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::record` | ADMIT LOCAL CONDITIONAL | 27 independent ranges in one semantic backing of length13831; all u8 rows; Same native/cohort caller carrier and installed dictionary association remain OPEN. Exact InvalidRow or selected pointer/length. Option-to-Result conversion is explicit. No borrowed-return stub or Prefix::parse closure. |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::sample_block_validated` | REJECT STATUS PROMOTION | next row agrees; tag/addition bounds; exact framed slice; Needs native three-call byte-slice log/unchanged replies and sequencing contract. RuntimeSha256Value supplies only values; never unwind/model SHA in Kani. |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::framed` | ADMIT LOCAL CONDITIONAL | one live readonly token; backing length 0..3717; Same native/cohort caller carrier and installed dictionary association remain OPEN. CLOSED only as a local getter; &[u8] substitution remains unsupported. Model parser acceptance proves cap, not native parser acceptance. |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::row` | REJECT STATUS PROMOTION | initial native packet covers five-byte backing only; Finding: five-byte backing excludes nonempty accepted records. No broader native domain credit; need repaired full-backing body/control/call-site packet. |
| `crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_query` | REJECT STATUS PROMOTION | start<=index<start+inverses.len; same five-field inverse row; Needs actual native borrowed fixed-array accessor contract/control and source/model association. Borrowed return cannot use current stub_verified machinery. |
| `crates/aspis-r1-cost-probe/src/verifier.rs::circle_fold_with_inverses` | REJECT STATUS PROMOTION | canonical field operands; five inverse cells from geometry; Needs exact native opaque-call log, every field stub paired with emitted-definition value law, and caller-proved domains. Import merged NDD field results only; no multiplication Kani. |
| `crates/aspis-r1-cost-probe/src/verifier.rs::line_fold_with_inverses` | REJECT STATUS PROMOTION | canonical field operands; same geometry inverses; Needs native opaque-call log and paired field-law/domain composition, including iz and half/quarter operations. No whole field-product proof in Kani; NDD owns field bridge work. |
| `crates/aspis-r1-cost-probe/src/verifier.rs::batch_prefix_products` | REJECT STATUS PROMOTION | flat length0..110; same Vec/prestate/product/index; Missing actual native one-append/one-multiply iteration with exact Vec frame/copy controls and log association. Vec return substitution is unsupported; field multiplication law is Lean-only. |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::state` | REJECT STATUS PROMOTION | native packet is monomorph NDF_NoDigest only; Finding: no actual deployed backend monomorph packet or proved native carrier transport. No digest was invoked; synthetic backend is not silently treated as deployed SolanaDigest. |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record` | REJECT STATUS PROMOTION | all rows; complete framed payload including row25; Native full validator contract remains unproved and borrowed Result substitution unsupported. Full parse_record accepted/tag/header assembly equality remains OPEN: the new validator equality and header word lemma are components, not a whole parser proof. NDF_AtCompose retains its explicit lower-parser equality hypothesis; it is not an enclosing certificate. |
| `crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::finish` | REJECT STATUS PROMOTION | destination length<=raw rows; canonical value law; Missing actual native one-destination-write iteration, raw/value callee-domain packet and mutable frame transport. Existing model induction does not prove native source loop. |
| `crates/aspis-r1-cost-probe/src/candidate.rs::parse_shape` | REJECT STATUS PROMOTION | arbitrary stored bytes, including wrong length/header/tail; Needs native seven-byte tail any one-iteration association plus symbolic short-circuit induction and complete Result mapping. No whole-loop substitution certificate was supplied by pilot. |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::new` | REJECT STATUS PROMOTION | public len representable u32; exact domain/length/root slices; Needs actual backend native digest-call byte-slice/reply transport and Result/record shape controls; runtime hash value remains trust. No SHA Kani. |
| `crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::raw` | REJECT STATUS PROMOTION | model: every N and bounded cursor; native candidate N32, bytes1768, at<=1736; Lean-only reference/cohort equality now complete. Native candidate timed out unchanged shape must not rerun. Split into one arbitrary byte/window and KMX frame/disjointness transport with a matched control; Kani budget exhausted. |
| `crates/aspis-r1-cost-probe/src/verifier.rs::read_checkpoint_semantic_alpha` | REJECT STATUS PROMOTION | ten checked K32-limb groups at actual checkpoint positions; Needs native scalar/fixed-array callee contracts, exact first-error/updated cursor sequence, and per-shape Result<([K;10],usize),Error> controls. raw native contract remains OPEN. |
| `crates/aspis-r1-cost-probe/src/verifier.rs::read_checkpoint_weights` | REJECT STATUS PROMOTION | actual mutable Vec<K>, bounded checkpoint cursor; Needs native one-element decode/write iteration and frame/source association. Vec-return verified substitution unsupported; raw/k native contracts remain OPEN. |
| `crates/aspis-r1-cost-probe/src/verifier.rs::validate_checkpoint_queries` | REJECT STATUS PROMOTION | 22 arbitrary query words; preserve first duplicate/range rejection; Needs actual native arbitrary i/prefix-membership iteration with invariant and model induction association, including rejection order. Whole22-buffer Kani is not the permitted loop method. |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::owner` | ADMIT LOCAL CONDITIONAL | bytes Err InvalidAccountData; length Ok arbitrary; arbitrary key/owner/flags; Same native/cohort caller carrier and installed dictionary association remain OPEN. Caller domain and physical interpretation remain OPEN. |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key` | ADMIT LOCAL CONDITIONAL | bytes Err InvalidAccountData; length Ok arbitrary; arbitrary key/owner/flags; Same native/cohort caller carrier and installed dictionary association remain OPEN. Caller domain and physical interpretation remain OPEN. |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_buffer_meta_ok` | ADMIT LOCAL CONDITIONAL | all three Bool inputs; exact ProgramError/Unit lift; Same native/cohort caller carrier and installed dictionary association remain OPEN. Caller domain and physical interpretation remain OPEN. |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data_len` | ADMIT LOCAL CONDITIONAL | length Ok arbitrary usize; bytes Err InvalidAccountData; Same native/cohort caller carrier and installed dictionary association remain OPEN. Caller domain and physical interpretation remain OPEN. |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data` | ADMIT LOCAL CONDITIONAL | bytes Ok singleton vector; all byte values; length Ok arbitrary or Err Custom; Same native/cohort caller carrier and installed dictionary association remain OPEN. Caller domain and physical interpretation remain OPEN. |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_meta_ok` | ADMIT LOCAL CONDITIONAL | all canonical Pubkeys and flags; cohort op36 comparison equals native byte comparison; Same native/cohort caller carrier and installed dictionary association remain OPEN. Caller domain and physical interpretation remain OPEN. |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::pool_program_id` | ADMIT LOCAL CONDITIONAL | 32-byte return; op45 represented by E001 pool_id_ref; selected installation association retained; Same native/cohort caller carrier and installed dictionary association remain OPEN. Caller domain and physical interpretation remain OPEN. |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::registry_program_id` | ADMIT LOCAL CONDITIONAL | 32-byte return; op46 represented by E001 registry_id_ref; selected installation association retained; Same native/cohort caller carrier and installed dictionary association remain OPEN. Caller domain and physical interpretation remain OPEN. |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::asq8_common` | REJECT STATUS PROMOTION | No complete native domain; See NDG_FRONTIER_BRIDGES.md: restricted native fragments or model-only results do not establish this enclosing body. |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_lane_from_pool_release` | REJECT STATUS PROMOTION | No complete native domain; See NDG_FRONTIER_BRIDGES.md: restricted native fragments or model-only results do not establish this enclosing body. |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::transfer_statement_box` | REJECT STATUS PROMOTION | No complete native domain; See NDG_FRONTIER_BRIDGES.md: restricted native fragments or model-only results do not establish this enclosing body. |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::withdrawal_statement_box` | REJECT STATUS PROMOTION | No complete native domain; See NDG_FRONTIER_BRIDGES.md: restricted native fragments or model-only results do not establish this enclosing body. |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer` | REJECT STATUS PROMOTION | No complete native domain; See NDG_FRONTIER_BRIDGES.md: restricted native fragments or model-only results do not establish this enclosing body. |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_zero` | REJECT STATUS PROMOTION | No complete native domain; See NDG_FRONTIER_BRIDGES.md: restricted native fragments or model-only results do not establish this enclosing body. |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot` | REJECT STATUS PROMOTION | No complete native domain; See NDG_FRONTIER_BRIDGES.md: restricted native fragments or model-only results do not establish this enclosing body. |

## Other merged and inherited results

- **NCV**: Primary op48/op49/op50 reference representations and slot selections are model results. Identity144 and policy predicates remain components; full native decoders and SDK caller association OPEN. Pinned reports: `evidence/native-decref-20261028/NCV_HANDOFF.md`.
- **NCX**: Current-format op33/op34 extracted bodies, lossless carriers, installations and complete fixture observations established. Restricted rejection/windows/status/zero/validator checks do not close native op33/op34; all accepted and remaining error classes, record/SDK association OPEN. Pinned reports: `evidence/native-decref2-20261028/NCX_HANDOFF.md`.
- **NDB**: 22 control-paired native component gates and primary reference window/loop/rejection laws. Full native op48/op49/op50 remains OPEN: original-wrapper same-input/context/Box/frame and complete model outcome assembly absent. Exclude memcmp unwind failures, K013 unpaired with stalled K014, failed Lean drafts. Pinned reports: `evidence/native-decnat-20261028/NDB_HANDOFF.md`.
- **KNF**: Reused static local-leaf replacement support and exact feature/body audit already present in NCZ. Does not lift historical Option<fn> quarantine. Pinned reports: .
- **KNG**: Reused 23 re-established property associations and parity receipts already present in NCZ. No extra coverage credit for counting the replacement twice; old quarantined receipts remain excluded. Pinned reports: .
- **NCN**: U10/U11 remain OPEN. Local valid64-row value helper improves NCI one-row domain; raw windows and iteration cuts are partial. NCN_K061 graph has no per-crate feature selection or independently associated reached-body parity for this new domain, so no additional deployed credit. Existing NCS/KNG-qualified NCI credit retained. K077 unpaired gives none. Pinned reports: `evidence/native-tx2r2-20261028/NCN_HANDOFF.md`.
- **NCJ**: U12/U13 remain OPEN. Guard/double/native iteration and sparse windows plus exact model arithmetic/Horner laws do not instantiate complete caller/loop/carrier/frame or free op ports. Whole finish_relation observer route retains K-2; no credit from pointer-dependent observations. Pinned reports: `evidence/native-tx2w-20261028/NCJ_HANDOFF.md`.
- **NCK**: Typed model owned/SDK/authentication composition, loops and accepted-domain coupling are established. Full native U15/U16, actual lower bridges, allocated carriers and same-SDK dispatch remain OPEN. Model free op11/op51/op52 laws cannot be inferred from types. Pinned reports: `evidence/native-tx2top-20261028/NCK_HANDOFF.md`.
- **NCM**: Stage1 complete CONDITIONAL TX1 batch/TX2 U09 composition with 18 native-step hypotheses. Stage2 has paired helper windows; none instantiates all 18 source cutpoint families. Whole batch/U09 OPEN; no new deployment credit from graph-only package/edge receipt lacking all-crate feature/body association. batch_key_at independently admitted through NDF. Pinned reports: `evidence/native-batchsk2-20261028/NCM_HANDOFF.md`.
- **NCT**: Accepted-cut model domain derives weights64/next10/canonical weights and same-call leaf, retaining S2,22 bounds,nine nonweight groups. Accepted-run quantifiers do not cover failed/diverging writers. Superseded in scope by NCU prefix factorization, not erased. Pinned reports: `evidence/native-drvdom-20261028/NCT_HANDOFF.md`.
- **NCU**: All-outcome model factorization and actual pre-writer prefix cover reached writers including fail/div. Same-prefix leaf retains S2,22 bounds,nine canonical groups plus local append/oracle/trace laws. Native reachability and source/ELF association remain OPEN. Pinned reports: `evidence/native-drvdom2-20261028/NCU_HANDOFF.md`.
- **NDA**: Same-prefix S2, all22 query bounds and distinctness, gamma/kappa/alpha/rho/semanticAlpha/claim canonicality established. domain_iff/remaining_iff reduce original domain EXACTLY to coordinates,rhs,power on that SAME cut. leaf retains those three groups or concrete primitive laws, plus unchanged local append/digest/oracle premises. Free-slot obstructions prevent silent concrete instantiation; native DriverEstablishedDomain remains OPEN. Pinned reports: `evidence/native-drvdom3-20261028/NDA_HANDOFF.md`.
- **NCP**: DigestDecode/canonicality/exact8,32 local witnesses retained as existing supplemental claims, without added deployed credit: graph summaries contain no exact per-crate feature association. Caller U03/U05 and encoder loops/validator remain OPEN; timeout/ICE/Vec substitution failures excluded. Pinned reports: `evidence/native-cpilot2-20261028/NCP_HANDOFF.md`.
- **KNH**: Kani0.68 candidate NOT adopted. K-1 false passes and K-2 name-sensitive verdicts persist, slice/Vec substitution unsupported, comparison incomplete and19 graph preflights missing. Tool probes give zero native/deployed credit; rule14 unchanged. Pinned reports: `evidence/kani-sandbox-20261028/KNH_EVALUATION.md`.
- **NCY**: Fresh devnet/Pool SBF artifact reproduction; default reused from NCR. No logical/native bridge closed; P7 and L188 source/feature/domain/final release audit remain. Artifact reproduction is not semantic correspondence. Pinned reports: `evidence/native-elfpins-20261028/NCY_HANDOFF.md`.
- **NDC**: Exact warned mangled instances omitted from linked final ELFs; no new P7 qualification recommended for those warnings. Omission is not fail-closed, whole runtime safety, indirect-call proof, privacy or native correspondence. Pinned reports: `evidence/native-sbfstack-20261028/NDC_HANDOFF.md`.
- **JHv**: Current-format registry authentication seventh child and SAME SDK validation composed, conditional on FixturePdaRuntime. Initial wrapper aggregation failed at import; superseded by JHw, not counted as native closure. Pinned reports: `evidence/joint-tx2fix3-20261028/JHv_HANDOFF.md`.
- **JHw**: Joint actual TX1/TX2 fixture acceptance on one saved vector established under JHe_SHARealization and FixturePdaRuntime, with explicit distinct heaps and same SDK. Model non-vacuity, not arbitrary-adversary native refinement. Pinned reports: `evidence/joint-agg2-20261028/JHw_HANDOFF.md`.
- **JHx**: 453 tree SHA equations proved; JHx_Joint.source removes only JHe_SHARealization, retains FixturePdaRuntime and identical joint conclusion. Fixture non-vacuity only, no native syscall/ELF/security theorem. Pinned reports: `evidence/joint-sha453-20261028/JHx_HANDOFF.md`.

No NDE_/NDH_/NDI_ artifact exists in this pinned merged tree. Unmerged work is not imported. KNF/KNG replacements were already counted: no double-count and no global quarantine lift. Historical quarantined harnesses remain listed verbatim in `quarantine`; mark and the release observer stay quarantined.

## Reproduction

`python3 evidence/native-ledger2-20261028/NDK_validate.py` reconstructs all rows, hashes, claims, evidence, graph and summary without rewriting. `--write` explicitly regenerates. `NDK_tests.py` reruns the inherited NCZ mutations on this snapshot and additional feature/theorem/control/delta/coverage/frontier checks. The original NCZ snapshot and files are retained unchanged; its full current-head CLI correctly refuses corpus drift.

Every selected new native run requires an exact single-harness positive or one semantic failed control, frozen lock/source checks, all-crate feature list and deployed helper/program selection. Each new theorem must match its successful archived source and exact standard-axiom audit. Python verifies these indexed assertions; manual statement/source association remains an audited trust boundary, not a new semantic prover. No Lean/Kani/Rust/SBF or host job ran here. No wallet/key operation.

## Current graph and inherited semantics


In canonical conservative union graph choose one OPEN/quarantined representative from each terminal SCC under reachability between OPEN SCCs. This is a minimum-cardinality reachability cover of all OPEN functions, not a dynamic/runtime critical path or a sufficient proof set.

Every terminal open SCC needs its own representative; no other open SCC can be reached downstream from it. Every open SCC reaches a terminal open SCC.

**Inventory caveat:** conservative arithmetic carrier unions include self/cyclic edges (e.g. CM31::add). These are retained, not pruned by guessed types. Ranking is advisory until carrier resolution is proved. Closing the frontier still leaves callers, domain transport, effects and physical interpretation to prove.

| Highest-impact OPEN function | Other inventory rows depending on it |
|---|---:|
| `crates/aspis-r1-cost-probe/src/weights.rs::field` | 31 |
| `crates/aspis-core/src/field.rs::qm31_pack_base4` | 29 |
| `crates/aspis-core/src/field.rs::CM31::square` | 28 |
| `crates/aspis-core/src/field/wide_exact.rs::WideExact::square` | 28 |
| `crates/aspis-statement/src/state_only_poseidon.rs::extension_from_raw_limbs` | 27 |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits` | 26 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::lift_m31` | 24 |
| `crates/aspis-statement/src/state_only_poseidon.rs::extension_limbs` | 23 |
| `crates/aspis-statement/src/state_only_poseidon.rs::pow5` | 23 |
| `crates/aspis-core/src/field.rs::QM31::neg` | 22 |

Minimum reachability-cover frontier: **130 SCC representatives**. Full members and all graph cycles are in JSON.

| Frontier representative | Dependent rows | OPEN functions in SCC |
|---|---:|---:|
| `crates/aspis-r1-cost-probe/src/weights.rs::field` | 31 | 1 |
| `crates/aspis-core/src/field.rs::qm31_pack_base4` | 29 | 1 |
| `crates/aspis-core/src/field.rs::CM31::square` | 28 | 1 |
| `crates/aspis-core/src/field/wide_exact.rs::WideExact::square` | 28 | 1 |
| `crates/aspis-statement/src/state_only_poseidon.rs::extension_from_raw_limbs` | 27 | 1 |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits` | 26 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::lift_m31` | 24 | 1 |
| `crates/aspis-statement/src/state_only_poseidon.rs::extension_limbs` | 23 | 1 |
| `crates/aspis-core/src/field.rs::QM31::neg` | 22 | 1 |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::index_at` | 22 | 1 |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed` | 22 | 1 |
| `crates/aspis-core/src/field.rs::qm31_accumulate_product_channels` | 21 | 1 |
| `crates/aspis-r1-cost-probe/src/sampler.rs::qm31_div_pass` | 21 | 1 |
| `crates/aspis-statement/src/state_only_poseidon.rs::external_local_packed_raw` | 21 | 1 |
| `crates/aspis-core/src/r0/merkle.rs::parent_with_digest` | 20 | 1 |
| `crates/aspis-core/src/state_only_private_merkle.rs::private_leaf_hash_with_digest` | 20 | 1 |
| `crates/aspis-r1-cost-probe/src/compact.rs::slot_offset` | 20 | 1 |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::occupied_binary_parent` | 20 | 1 |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::root_matches` | 20 | 1 |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::sibling_binary_parent` | 20 | 1 |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::value_at` | 20 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::update_residue_row` | 20 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::empty_root` | 20 | 1 |
| `crates/aspis-core/src/r0/heap.rs::filled` | 19 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::sum_high` | 19 | 1 |
| `crates/aspis-statement/src/poseidon2.rs::apply_mat4_lazy` | 19 | 1 |
| `crates/aspis-core/src/r0/domain.rs::FibreIndex::get` | 18 | 1 |
| `crates/aspis-r1-cost-probe/src/candidate.rs::batch_keys` | 18 | 1 |
| `crates/aspis-r1-cost-probe/src/candidate.rs::sort_batch_keys` | 18 | 1 |
| `crates/aspis-r1-cost-probe/src/fast_domain.rs::table_value` | 18 | 1 |
| `crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots_one` | 18 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::mark` | 18 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::bounded_append_carry` | 18 | 1 |
| `crates/aspis-statement/src/poseidon2.rs::internal_linear_lazy` | 18 | 1 |
| `crates/aspis-statement/src/poseidon2.rs::pow5` | 18 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::row` | 17 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_tag_coordinate_dot` | 17 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::lift_m31` | 17 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::absorption_lanes_factored` | 17 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::initial_variant_selectors` | 17 | 1 |
| `crates/aspis-statement/src/pool_v1/verifier_registry.rs::required_binding_is_zero` | 17 | 1 |
| `crates/aspis-statement/src/state_only_poseidon.rs::interpolate_three_constant_limb` | 17 | 1 |
| `crates/aspis-core/src/field.rs::qm31_m31_dot` | 16 | 1 |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::sample_block_validated` | 16 | 1 |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::row` | 16 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_query` | 16 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::circle_fold_with_inverses` | 16 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::line_fold_with_inverses` | 16 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::active_mask_basis` | 16 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::expand` | 16 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::finish_pattern_basis_values` | 16 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::selected_binary_weight` | 16 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::path_lanes_factored` | 16 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::reconstruct_10` | 16 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::variant_expected_output` | 16 | 1 |
| `crates/aspis-core/src/field.rs::CM31::inv_with` | 15 | 1 |
| `crates/aspis-core/src/field.rs::qm31_sum_products3_prepared` | 15 | 1 |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::validated_record` | 15 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_residual` | 15 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::link_weight` | 15 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::private_public` | 15 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::scalar_lanes` | 15 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::withdrawal_public` | 15 | 1 |
| `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::has_no_retirement_slot` | 15 | 1 |
| `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::has_no_retirement_slot` | 15 | 1 |
| `crates/aspis-core/src/field/wide_exact.rs::WideExact::neg` | 14 | 1 |
| `crates/aspis-core/src/r0/domain.rs::FibreIndex::new` | 14 | 1 |
| `crates/aspis-core/src/r0_transcript.rs::block_rank` | 14 | 1 |
| `crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::absorb` | 14 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::batch_prefix_products` | 14 | 1 |
| `crates/aspis-r1-cost-probe/src/weights.rs::Weights::scalar_factor` | 14 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::copy_variant` | 14 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::selected_claim` | 14 | 1 |
| `crates/aspis-core/src/state_only_hiding.rs::cm31_mul_r` | 13 | 1 |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_value` | 13 | 1 |
| `crates/aspis-r1-cost-probe/src/sampler.rs::decode8` | 13 | 1 |
| `crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1` | 13 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::equality_value` | 13 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes::fields` | 13 | 1 |
| `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_immutable` | 13 | 1 |
| `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_immutable` | 13 | 1 |
| `crates/aspis-core/src/r0_transcript.rs::QueryScan::finish` | 12 | 1 |
| `crates/aspis-core/src/state_only_hiding.rs::selected_mask_linears` | 12 | 1 |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::state` | 12 | 1 |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record` | 12 | 1 |
| `crates/aspis-r1-cost-probe/src/sampler.rs::add_small_base_p` | 12 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::finish` | 12 | 1 |
| `crates/aspis-r1-cost-probe/src/weights.rs::Weights::tensor` | 12 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pool_v1_pair_live_snapshot_v1` | 12 | 1 |
| `crates/aspis-core/src/state_only_prefix.rs::state_only_statement_points` | 11 | 1 |
| `crates/aspis-r1-cost-probe/src/candidate.rs::parse_shape` | 11 | 1 |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs::mark` | 11 | 1 |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::payload` | 11 | 1 |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::new` | 11 | 1 |
| `crates/aspis-r1-cost-probe/src/weights.rs::high_dot` | 11 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pair_afterstate_boxed_v1` | 11 | 1 |
| `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierEntryStatusV1::try_from` | 11 | 1 |
| `crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::new` | 10 | 1 |
| `crates/aspis-r1-cost-probe/src/weights.rs::Weights::box_from_parts` | 10 | 1 |
| `crates/aspis-r1-cost-probe/src/weights.rs::double` | 10 | 1 |
| `crates/aspis-r1-cost-probe/src/weights.rs::shared_two_point_guard` | 10 | 1 |
| `crates/aspis-statement/src/pool_v1/format.rs::decode_pool_identity_v1` | 10 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts` | 10 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer` | 10 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint` | 10 | 1 |
| `crates/aspis-r1-cost-probe/src/compact.rs::expand_semantic` | 9 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::raw` | 9 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::read_checkpoint_semantic_alpha` | 9 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::read_checkpoint_weights` | 9 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::validate_checkpoint_queries` | 9 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_checkpoint_v1` | 9 | 1 |
| `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_paused` | 9 | 1 |
| `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_paused` | 9 | 1 |
| `programs/r1-cost-probe/src/lib.rs::observer` | 9 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account` | 9 | 1 |
| `crates/aspis-r1-cost-probe/src/candidate.rs::canonical_scan` | 8 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_transfer_statement_boxed_v1` | 8 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_withdrawal_statement_boxed_v1` | 8 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::asq8_common` | 8 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_lane_from_pool_release` | 8 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::transfer_statement_box` | 8 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::withdrawal_statement_box` | 8 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1` | 7 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_result_v1` | 7 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_result_against_statement_v1` | 7 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer` | 7 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::semantic_public` | 6 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_zero` | 6 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot` | 6 | 1 |
| `programs/r1-cost-probe/src/pool_route.rs::admitted` | 2 | 1 |
