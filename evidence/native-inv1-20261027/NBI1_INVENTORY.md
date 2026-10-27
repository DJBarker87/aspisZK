# NBI1 TX1 native bridge inventory

Static inventory, frozen Rust `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.
Headline: `AspisR1.RPx_Deployed.deployed`. No premise removed. L154 remains a
statement parameter; narrowed D188, frozen3, RuntimePersistence and the approved
two-transaction game are unchanged. S2 / the deployed 100-bit target remain
**not established**. Bridge units below are proposals, not new bridge proofs.

## Findings first: missing separate cohort counterparts

The JSON `no_separate_counterpart` list and the table immediately below give
EVERY inventoried source function for which this search found no separate
executable counterpart in the replayed headline closure. These are modelling
granularity/association gaps to account for in the proposed caller bridge;
absence of a separate function does not establish that its behavior is absent
from an enclosing model. Do not fill them by assuming a whole caller result.

Priority caller gaps are release admission (`pool_route::admitted`), adapter
`process`, `snapshot`, and `decode_public_statement_box`. The adopted proofs
instead compose the driver/SDK entry, an owned account model, the decoder and
trusted copy/borrow contracts. A native bridge must connect the actual dispatch,
metadata, snapshot allocation/copy/Drop and fixed decoder call to those same
carriers. The snapshot has no oracle call, but its byte identity and lifetime
matter to every later oracle input. `stage1`'s final mutable account borrow/copy
and cleanup must remain in the same execution. No SDK or allocator admission
is discharged here.

Other unseparated helpers include scanner `echeck`, compact `expand_values`,
several binary multiproof/index helpers, inverse-fold helpers and scalar/byte
projections. `echeck` and `expand_values` already have CLOSED local native leaf
packets; their *caller installation* is still a bridge edge. The absence of
those names from this particular replay closure does not reopen their leaf
proofs or authorize replacing the adopted cohort. This inventory identifies
which enclosing scan/expansion/verification unit must consume their laws.

## Frozen release scope and path

The authoritative build commands are
`evidence/sbf-identity-20261024/recapture-plan.json`: BOTH default and devnet
verifier builds use `programs/r1-cost-probe` with
`pool-adapter,private-leaf-salts` (plus default custom heap and the dependency's
optimized-terminal feature expansion). Their only accepted TX1 instruction is
`[3,10]`. `[3,11]` reaches `tx1` but rejects its `k != SPLIT` gate. The legacy
`[1,k]`/`[2]` branch is cfg-excluded from these releases. ASQ8 is TX2; it is not
a TX1 request validator. The Pool ELF is built separately with
`r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit`;
Pool settlement/ASQ8/CPI is not executed by the standalone first transaction.
This corrects the worker's early commentary that confused Cargo defaults with
the named default release artifact.

Accepted TX1 source order:

1. Solana entrypoint macro → `process_r1_cost_probe_instruction` →
   `pool_route::admitted` → adapter `process` → owned `stage1`.
2. Instruction/account-count checks; three snapshots; `stage1_owned` checks
   distinct keys, proof/public readonly metadata, checkpoint owner/writable/
   nonsigner/nonexecutable/length and all-zero checkpoint.
3. Decode and validate the same public1880; encode its candidate afterstate688;
   check proof account58295 and candidate prefix; select suffix57607; obtain
   `statement.semantic_public()`; call `first_decoded` with physical public
   bytes, exact suffix, split10, SolanaDigest and observer None.
4. `candidate::tx1`: shape → full canonical scan → logical allocation and
   expansion → semantic prefix/transcript/rounds/terminal → Prepared constructor
   and same powers29 scratch → accumulator64 → batch0's three binary multiproofs
   → geometry for queries0..10 → pending weights → ten query steps → flush
   SAME weights → checkpoint writer (proof, physical public, labelled body
   digest in that order) → bytes1768.
5. Owned wrapper checks returned length; SDK wrapper copies those same bytes
   into account2 and releases guards/temporary allocations. Runtime admission,
   ABI, syscall/oracle, snapshot/copy/Drop and source-to-ELF joins remain explicit.

The source walk stops expansion at all13 CLOSED opaque leaves, while still
recording each leaf body's own call sites and loop/effect inventory. Leaf
packets may themselves contain further internal calls; those are not reopened.
Audit-only eight_way, prover/examples, profiling, lifecycle and TX2 branches are
excluded. Source-level branches in a reached function whose test depends on an
abstract argument are conservatively retained, including field-carrier overload
support; this is a static call inventory, not a compiler-certified reachability
or accepted-execution proof. Every ambiguous field edge is labelled in JSON;
no overloaded carrier is silently equated. Builtin/derived traits, iterator
machinery and external SDK methods have call-site records rather than invented
Rust source bodies.

## How to use the inventory

`NBI1_INVENTORY.json` is the detailed machine-readable artifact. Each function
has frozen file/line/end-line, exact byte ranges, body/function SHA256, call
expressions and lines, resolved source targets, cohort names/modules/source
locations, loops, iterator operations, explicit mutable references and mutable
signature, field operations, digest calls, bridge unit and callee-domain edges.
The Markdown tables index the same facts. Function-value callbacks and inline
closures are part of their enclosing body; the generic CM31 inversion callback
remains an explicitly bound function-pointer parameter. FibreIndex's two methods
come from the frozen `index_type!` template with bound262144; their hash is the
original template body, not an invented post-expansion file.

Body SHA256 covers the exact UTF-8 bytes from opening `{` through closing `}`,
including whitespace/comments but excluding signature/attributes. Function SHA
is also in JSON. This convention can differ from older leaf packet whole-range
hashes without implying a source delta. All345 selected function spans and all
270 inspected frozen source files are checked against local bytes.

Cohort names are filtered by the **actual reachable constants** of
`evidence/replay-deployed2-20261027/RPx_reachable-constants.json`, cross-checked
against replay-tops3. Their modules are taken from the retained declaration
axiom audits in that replay's inherited chain; namespace similarity alone does
not count. The model index retains the owner audit and exact local source
location/hash. Multiple names mean multiple nominal cohort owners actually
used in the closure, not a proof that their types are interchangeable. Explicit
aliases (e.g. PreparedScratchModel.prepare, Port3_FlushInstall.flush,
CheckpointBytes5Writer.writer) identify installed/reified cohort computations;
they are not claims of literal Aeneas extraction of the corresponding Rust body.
No XRn_Join kit, join stand-in, live session A worktree or candidate was used.

## Leaf domains to establish in callers

| CLOSED leaf | Caller obligation (same actual operands) | Authoritative packet |
|---|---|---|
| low_base_p_digits | arbitrary exact32-byte block | leaf-sampler1-20261027/LPk_LEAF.md |
| echeck | input length≤2272; both k; caller lengths32/224/2272/128 | leaf-p6-10-20261027/LPl_echeck_LEAF.md |
| check_values | actual464-byte compact y1; all bytes, including rejection | leaf-p6-10-20261027/LPl_check_values_LEAF.md |
| expand_values | source0..1856/output0..3712; actual paired buffers, including length errors | leaf-p6-12-20261027/LPn_expand_values_LEAF.md |
| validate_record_fields | payload0..3712, same row and first bad index | leaf-p6-10-20261027/LPl_validate_record_fields_LEAF.md |
| ValidatedRecord.decode_k | genuine framing≥5, N1/28/29; source byte/offset arithmetic and same token; reached offsets0/29/58/87 | leaf-p6-12-20261027/LPn_decode_k_LEAF.md |
| claims | genuine adopted Prefix row25 and same allocation/three source decodes, retained allocation/ownership qualification | leaf-p6-12-20261027/LPn_claims_LEAF.md |
| canonical Dot.push | private-Q canonical operands from actual checked producer, arbitrary U64 sums/state; same dot history | leaf-p6-12-20261027/LPn_Dot_push_LEAF.md |
| wide_view | exact proof57607/logical semantic13831/y1 928, source slices/lifetimes; native decoder Result | leaf-p6-13-20261027/LPo_wide_view_LEAF.md |
| semantic_boundary | same decoded28 canonical coefficients; coefficient0 is seed and visited again | leaf-p6-13-20261027/LPo_semantic_boundary_LEAF.md |
| circle_sample closure | arbitrary32-byte block, either CircleRow; native inverse/fallback domain as LPp; closure subclaim is not a replacement for all sampler producers | leaf-p6-14-20261027/LPp_circle_sample_LEAF.md |
| checkpoint | existing S1S7S8StateProvenance: S2,next10,weights64,22 queries<262144, canonical saved fields and agreement with same reached state; unchanged proof/public | leaf-p6-11-20261027/LPm_checkpoint_LEAF.md |
| prepared_claim | LPt ByteDomain.natural on same compact464/initial928/check_values success/native expansion; same successful installed semantic finish; canonical gamma/inactive/kappa and actual returned powers29(gamma) | leaf-p6-18-20261027/LPt_prepared_claim_LEAF.md |

For each remaining loop: one native iteration on an arbitrary invariant-bearing
pre-state, Lean induction, then native/model step association. Never whole-buffer
Kani. Field multiplication is never a Kani gate: reuse the named LPh/LPi/LPm/LPq
stub-value pairings and prove their canonical domains at each call. No new stub,
theorem, harness or stronger caller precondition is introduced by this inventory.

## No separate counterpart: complete row list

| Unit | Functions (exact source pins in the function table) |
|---|---|
|accumulate|F183 `accumulated_weight_at`, F184 `basis_at`|
|control|F130 `mark`, F171 `final_len`|
|entry|F331 `admitted`|
|field|F027 `inv`, F031 `neg`, F036 `qm31_accumulate_product_channels`, F040 `qm31_sum_products2`, F041 `qm31_sum_products3`, F043 `qm31_sum_products4`, F044 `qm31_sum_products_small`, F054 `neg`, F056 `square`|
|geometry|F063 `new`, F102 `line_node`, F180 `for_query`|
|keys|F078 `batch_key_at`|
|leaf:echeck|F189 `echeck`|
|leaf:expand_values|F099 `expand_values`|
|multiproof|F065 `parent_with_digest`, F077 `private_leaf_hash_with_digest`, F118 `bits`, F119 `levels`, F120 `width`, F121 `index_at`, F123 `occupied_binary_parent`, F124 `root_matches`, F125 `sibling_binary_parent`, F126 `value_at`, F128 `well_formed`|
|opening-transcript|F067 `scan`, F069 `queries_from_pairs`|
|parser|F139 `payload`|
|public-codec|F268 `semantic_public`|
|public-hash|F201 `pool_v1_tree_parent`, F202 `default`, F203 `empty`, F204 `pool_v1_empty_roots`, F302 `apply_mat4_lazy`, F303 `external_linear_lazy`, F304 `internal_linear_lazy`, F305 `merkle_node_compress_v3`, F306 `permute_optimized_with_trace`, F307 `pow5`|
|query|F188 `circle_fold_with_inverses`, F190 `line_fold_with_inverses`|
|residue|F192 `power_limb_at`, F194 `residue_limb_at`, F195 `update_residue_row`|
|semantic-eval|F209 `active_mask_basis`, F214 `accumulate_endpoint_selector_tensor_basis`, F216 `copy_tag_coordinate_dot`, F217 `copy_tag_coordinate_value`, F219 `finish_pattern_basis_values`, F220 `finish_selector_tensor_basis`, F224 `pattern_values_windowed`, F225 `qm31_sum_products_up_to4`, F226 `selected_binary_weight`, F227 `absorption_lanes_factored`, F231 `add_preweighted_shared_selector`, F234 `append_level_packed_selector_tensor`, F235 `append_levels_packed_selector_tensor`, F242 `left_digest_packed_selector_tensor`, F244 `occupancy_lanes_factored`, F245 `optional_carry_packed_selector_tensor`, F246 `optional_recipient_packed_selector_tensor`, F247 `path_lanes_factored`, F250 `public_digest_packed`, F251 `public_digest_packed_selector_tensor`|
|semantic-transcript|F133 `semantic_round`, F134 `semantic_rounds`|
|wrapper|F187 `checkpoint_size`, F332 `decode_public_statement_box`, F333 `process`, F343 `snapshot`|

## Proposed bridge units, bottom-up

S/M/L are engineering sizing only, not measured prover runtimes. Each unit lists its member rows and callee bridges. Its domain is what the caller must establish; callee-domain obligations in JSON point to these same domains. Small helpers and inline callbacks are merged with the indicated caller. CLOSED leaf units retain their packet domains. No unit in this table is newly proved.

| Order | Unit / size | Members | Callee bridges | Required domain |
|---|---|---|---|---|
|1|`control` S — Release no-op observers, trace and Variant projections|F130, F164, F171, F172, F173, F191, F329||Release observer None, trace compiled out; S2 tag2/folds2/final_len64. No callback or oracle effect. Small projections merge into each caller.|
|2|`field` M — Field and scalar carriers|F001, F002, F003, F004, F005, F006, F007, F008, F009, F010, F011, F012, F013, F014, F015, F016, F017, F018, F019, F020, F021, F022, F023, F024, F025, F026, F027, F028, F029, F030, F031, F032, F033, F034, F035, F036, F037, F038, F039, F040, F041, F042, F043, F044, F045, F046, F047, F048, F049, F050, F051, F052, F053, F054, F055, F056, F057, F058, F059, F060, F061, F196||Canonical natural coordinates; retain exact packed carriers, checked overflow and error behavior. Multiplication uses only Lean-discharged stubs with named emitted-definition value theorems (LPh_STUBS and descendants).|
|3|`alloc` M — Allocation and buffer initialization|F064||Pinned allocator/library admission; successful length and full initialized carrier, with Allocation/abort behavior retained.|
|4|`residue` L — Batched residue initialization/update/flush|F175, F176, F177, F178, F192, F194, F195|alloc, field|64 canonical initial weights; raw rows U64; terms tracks same query count, at group boundary limbs<2^34; each update adds canonical power*basis without overflow; flush when terms&3=3. Finish reduces same raw rows into same64-weight allocation.|
|5|`accumulate` L — Basis and accumulator one query step|F182, F183, F184|control, field, residue|S2 width64, next i<10; same pending terms=i, same rhs/power; canonical fold/node/rho and basis; establish raw update invariant, next=i+1, power/rhs exact and original weights retained until flush.|
|6|`oracle` S — Concrete digest backend|F327||SolanaDigest::digest uses pinned hashv syscall; same parts/order and arbitrary32-byte replies under retained P1/runtime syscall trust. No SHA unwinding.|
|7|`multiproof` L — Binary multiproof scan and in-place verifier|F065, F077, F118, F119, F120, F121, F122, F123, F124, F125, F126, F127, F128|oracle|Arity Two only; 1<=d<=10<=16, sorted distinct idx<2^18; exact node_count words within fixed slot, zero padding. Retain mutable idx/val alias/frame and chronological leaf/parent digests.|
|8|`leaf:expand_values` S — expand_values (CLOSED)|F099||Use leaf-p6-12-20261027/LPn_expand_values_LEAF.md verbatim on this SAME source carrier; see leaf domain table.|
|9|`leaf:validate_record_fields` S — validate_record_fields (CLOSED)|F154||Use leaf-p6-10-20261027/LPl_validate_record_fields_LEAF.md verbatim on this SAME source carrier; see leaf domain table.|
|10|`parser` M — Prefix/record parser and semantic expansion|F097, F098, F100, F138, F139, F140, F141, F148, F149, F151, F152, F153|leaf:expand_values, leaf:validate_record_fields|Stored proof length57607; semantic compact range to logical13831; row framing and exact same Prefix token; LPn expansion 0..1856/0..3712; validation payload0..3712; decode N=1/28/29 and reached offsets0/29/58/87.|
|11|`keys` M — Batch sort, opening and slot helpers|F078, F079, F080, F085, F090, F091, F092, F093|multiproof, parser|Batch0,n10,tree0/1/2; queries<262144; stable position keys; sorted unique output prefix with folded duplicates carrying identical leaves; exact source slices.|
|12|`batch` L — Three batch-tree calls|F081, F082, F083|keys, multiproof|Same prepared queries/roots and folded root; batch0 trees0,1,2; keys/dedup/count/padding establish each multiproof domain; same shared idx/val scratch and ordered oracle log.|
|13|`leaf:push:canonical::Dot` S — push (CLOSED)|F111||Use leaf-p6-12-20261027/LPn_Dot_push_LEAF.md verbatim on this SAME source carrier; see leaf domain table.|
|14|`dots` L — Four query dots and EbyK carrier helpers|F104, F105, F106, F107, F108, F109, F110, F112, F113, F114, F115, F116, F117|field, leaf:push:canonical::Dot|Exact opening832 (dot prefix608), g29 canonical from same powers; 26 base terms plus three K tails per slot; private-Q canonicality; count<4096; reuse LPn Dot.push on same state, not independent dots.|
|15|`geometry` L — Domain tables and query geometry|F062, F063, F101, F102, F103, F180, F181, F185|field|22 distinct query indices<262144; 0<=start<=end<=22, TX1 start0/end10; five nonzero denominators per query, flat length50. Prove nonzero product and indexed inverse vector association.|
|16|`leaf:checkpoint` S — checkpoint (CLOSED)|F186||Use leaf-p6-11-20261027/LPm_checkpoint_LEAF.md verbatim on this SAME source carrier; see leaf domain table.|
|17|`leaf:wide_view` S — wide_view (CLOSED)|F095||Use leaf-p6-13-20261027/LPo_wide_view_LEAF.md verbatim on this SAME source carrier; see leaf domain table.|
|18|`leaf:prepared_claim` S — prepared_claim (CLOSED)|F193||Use leaf-p6-18-20261027/LPt_prepared_claim_LEAF.md verbatim on this SAME source carrier; see leaf domain table.|
|19|`public-hash` L — Poseidon and tree/public validation helpers|F198, F199, F200, F201, F202, F203, F204, F302, F303, F304, F305, F306, F307, F308, F309, F310, F311, F312, F313, F314, F315, F316, F317, F318, F319, F320, F321, F322, F323, F324, F325, F326|field|Canonical M31 inputs and exact fixed-width public/tree state; no reselected root or replacement public serialization.|
|20|`leaf:low_base_p_digits` S — low_base_p_digits (CLOSED)|F159||Use leaf-sampler1-20261027/LPk_LEAF.md verbatim on this SAME source carrier; see leaf domain table.|
|21|`sampler` M — Sampler wrappers and digit helpers|F155, F157, F158, F160, F161, F162, F163|field, leaf:low_base_p_digits|Arbitrary exact 32-byte block; LPk low digits on same block; ordinary/gamma canonicality and gamma nonzero. Preserve modulo/carry and typed result.|
|22|`leaf:circle_sample` S — circle_sample (CLOSED)|F156||Use leaf-p6-14-20261027/LPp_circle_sample_LEAF.md verbatim on this SAME source carrier; see leaf domain table.|
|23|`leaf:claims` S — claims (CLOSED)|F129||Use leaf-p6-12-20261027/LPn_claims_LEAF.md verbatim on this SAME source carrier; see leaf domain table.|
|24|`leaf:decode_k:ValidatedRecord<'a>` S — decode_k (CLOSED)|F147||Use leaf-p6-12-20261027/LPn_decode_k_LEAF.md verbatim on this SAME source carrier; see leaf domain table.|
|25|`leaf:semantic_boundary` S — semantic_boundary (CLOSED)|F132||Use leaf-p6-13-20261027/LPo_semantic_boundary_LEAF.md verbatim on this SAME source carrier; see leaf domain table.|
|26|`semantic-eval` L — S1 public/Copy/semantic terminal helpers|F071, F072, F073, F074, F075, F076, F208, F209, F210, F211, F212, F213, F214, F215, F216, F217, F218, F219, F220, F221, F222, F223, F224, F225, F226, F227, F228, F229, F230, F231, F232, F233, F234, F235, F236, F237, F238, F239, F240, F241, F242, F243, F244, F245, F246, F247, F248, F249, F250, F251, F252, F253, F254, F255, F256, F257, F258, F259, F260, F261, F262, F263, F264, F265, F266|field, public-hash|Same Public, genuine parsed Claims, alpha/challenges and actual canonical decoder outputs. Reuse S1 cohort theorems read-only; native association of every helper and loop remains a caller obligation.|
|27|`semantic-transcript` L — Semantic transcript and rounds|F131, F133, F134, F135, F136, F137, F142, F143, F144, F145, F146, F150|control, field, leaf:circle_sample, leaf:claims, leaf:decode_k:ValidatedRecord<'a>, leaf:semantic_boundary, oracle, parser, sampler, semantic-eval|Same valid Prefix/public bytes; row-ordered blocks, two CircleRows and arbitrary digest replies; canonical 28-coefficient polynomial from same decode. Preserve first error and every attempted oracle call.|
|28|`opening-transcript` L — Opening transcript and Prepared constructor|F066, F067, F068, F069, F070, F165, F166, F167, F168, F169, F170, F179, F197|control, field, leaf:prepared_claim, oracle, public-hash, sampler, semantic-transcript|Same successful semantic finish; exact y1 length928/inactive32/round224/root32/final2048. Establish sampler domains, powers29 output identity, LPt compact464 checked/expanded same carrier, canonical kappa/gamma/inactive.|
|29|`prepare` L — Logical allocation and verifier prepare|F087|alloc, control, leaf:expand_values, leaf:wide_view, opening-transcript, parser, semantic-transcript|Same proof57607, validated Public and immutable physical public1880; logical buffer14759 split13831/928 with disjoint mutable windows. Produce actual semantic finish and prepared/g29 once; prove all leaf/callee domains from scan.|
|30|`query` L — Query values and loop|F088, F089, F188, F190|accumulate, control, dots, field, geometry, keys|Same authenticated batch0/proof/Prepared/g29; geometry start0/end10; accumulator.next=i and pending terms=i, i<10; dots/folds compare same selected field, preserve rejection and observer None. One arbitrary native step plus Lean induction to next10.|
|31|`leaf:check_values` S — check_values (CLOSED)|F096||Use leaf-p6-10-20261027/LPl_check_values_LEAF.md verbatim on this SAME source carrier; see leaf domain table.|
|32|`leaf:echeck` S — echeck (CLOSED)|F189||Use leaf-p6-10-20261027/LPl_echeck_LEAF.md verbatim on this SAME source carrier; see leaf domain table.|
|33|`shape` M — Shape and canonical scan|F084, F086|control, field, keys, leaf:check_values, leaf:echeck|Proof57607 and S2 magic/header; check_values464; echeck32/224/2272/128; all22 openings832, every M31/K field canonical; preserve first Parse.|
|34|`driver` L — TX1 composition to checkpoint writer|F094, F174|alloc, batch, control, geometry, leaf:checkpoint, prepare, query, residue, shape|All predecessors from same accepted run; k10,S2; accumulator next10/64 canonical weights after flush, queries22<2^18; LPm exact p/a/proof57607/public1880 with three ordered digests and output1768; no independently supplied checkpoint.|
|35|`public-codec` L — Public statement decode, validation and afterstate encode|F205, F206, F207, F267, F268, F269, F270, F271, F272, F273, F274, F275, F276, F277, F278, F279, F280, F281, F282, F283, F284, F285, F286, F287, F288, F289, F290, F291, F292, F293, F294, F295, F296, F297, F298, F299, F300, F301|field, public-hash|Same 1880-byte public buffer, successful fixed decoder; validated statement and same 688-byte encoded candidate. All branch-specific Transfer/Withdrawal guards and digest/field bounds.|
|36|`wrapper` L — SDK first wrapper and owned outer body|F187, F328, F332, F333, F334, F335, F336, F337, F338, F339, F340, F341, F342, F343, F344, F345|control, driver, public-codec|One runtime-admitted execution, three distinct accounts; readonly proof58295/public1880, writable program-owned zero checkpoint1768, allowed borrow counters and retained keys; candidate prefix688, suffix57607 and k10; snapshot/write/drop/metadata/frame and exact child effects under approved SDK trust.|
|37|`entry` M — Entrypoint and release dispatch|F330, F331|wrapper|Pinned release features pool-adapter,private-leaf-salts for BOTH default/devnet; [3,10] accepted ([3,11] reaches child rejection); account gates, same original input bytes and observer None; distinguish default route from adopted Pool headline admission.|

## Every inventoried function

Callees are row IDs; a stopped leaf can also have internal targets outside this inventory, retained verbatim in JSON. Standard-library/runtime calls and inline callbacks are in each row's JSON call-site list. “Loop” lists explicit loop lines; I marks iterator combinators; B marks mutable signature/borrows; F names field calls; O names direct digest calls. Indirect callee effects compose through the listed edges. Body hashes are full SHA256. Cohort IDs resolve to exact Lean names/modules below; an empty cohort is explicitly “no cohort counterpart”.

| Row / function | Frozen file:line | Body SHA256 | Callees | CLOSED leaf | Cohort | Loops / borrows / field / oracle | Unit |
|---|---|---|---|---|---|---|---|
|F001 `CM31::add`|`crates/aspis-core/src/field.rs:281`|`feead0d400d9868283096c65b03d3e31d7c6b996bc9877eb6bd1ed239745a953`|F001|no|M071,M164,M192,M222,M315,M351,M364,M405|F add|field|
|F002 `CM31::double`|`crates/aspis-core/src/field.rs:346`|`3a024536ab8e6cf0a01211d509e16b0927e3c397267ca8046a05c9c2a13f54c7`|F001|no|M193,M316,M365,M406|F add|field|
|F003 `CM31::from_le_bytes`|`crates/aspis-core/src/field.rs:410`|`d87b6a001eb6ba955869857f651ee6d3191328b8141b75dd9d71f3dc2023b42a`|F015|no|M019,M053,M094,M498|none|field|
|F004 `CM31::from_m31`|`crates/aspis-core/src/field.rs:276`|`96ed271e1bfeb85a0dec133bc4b4357c57df79a004b28c551474daa22a07887f`||no|M340,M341,M407|none|field|
|F005 `CM31::inv`|`crates/aspis-core/src/field.rs:390`|`2030a2aafd1b2499ad9a0340979bcf954a77216629fa2fbd90ee615c4634448d`|F006|no|M317|none|field|
|F006 `CM31::inv_with`|`crates/aspis-core/src/field.rs:396`|`6bdba26e9d83c5f0214835961eadc9974a6033574502b7d24ef8e3954792790b`|F001,F007,F009|no|M318|F add,mul,neg|field|
|F007 `CM31::mul`|`crates/aspis-core/src/field.rs:306`|`a9676bf974a9b2cda0d0bf13d9f0b4f56a4f849ba430835eb71e151055ed9e0d`|F007,F012,F020|no|M072,M165,M194,M223,M319,M352,M366,M408|F M31::reduce_u64,mul,sub|field|
|F008 `CM31::mul_m31`|`crates/aspis-core/src/field.rs:338`|`4a87bf432c390be73d40c66b14f51f02298bf73b2187bd8216d0e8c53d54d79a`|F007|no|M073,M195,M367,M409|F mul|field|
|F009 `CM31::neg`|`crates/aspis-core/src/field.rs:297`|`34b33b1ed28378cd76546671307a667c7c6498212f63d4766067d96492d436e0`|F009|no|M320|F neg|field|
|F010 `CM31::new`|`crates/aspis-core/src/field.rs:271`|`b82314af9377ead49dc46747df4755c001e0ab79446d7a23becc94f74cc056d8`||no|M111,M132,M176,M196,M321,M410|none|field|
|F011 `CM31::square`|`crates/aspis-core/src/field.rs:325`|`04ca6d35e6deabc92b30a4b9c69677ea90d0ec68418e5766ac18908a5d017bdd`|F002,F007,F020|no|M197,M322,M368,M411|F M31::reduce_u64,double,mul|field|
|F012 `CM31::sub`|`crates/aspis-core/src/field.rs:289`|`efdf12c5739fe6362e1a3cb7267b05178ecf03ecffce6ae841a45907328d2734`|F012|no|M074,M166,M198,M224,M323,M353,M369,M412|F sub|field|
|F013 `M31::add`|`crates/aspis-core/src/field.rs:62`|`c7afbab359feb4c3a6b41a005a77541b454825cae6258f0f7c752e5840f1bca6`||no|M075,M167,M199,M225,M301,M307,M324,M354,M370,M413|none|field|
|F014 `M31::double`|`crates/aspis-core/src/field.rs:183`|`3a024536ab8e6cf0a01211d509e16b0927e3c397267ca8046a05c9c2a13f54c7`|F013|no|M076,M168,M200,M226,M325,M355,M371,M414|F add|field|
|F015 `M31::from_le_bytes`|`crates/aspis-core/src/field.rs:239`|`11700e1c990379b281c28c30bd0bd3afaf5bb4d74a265f683cff745327ef2f68`||no|M020,M054,M095,M108,M239,M348,M499|none|field|
|F016 `M31::inv`|`crates/aspis-core/src/field.rs:213`|`d58a157083d8bce112deaa5cdac1461b6454c47209725dd1b8bcacabf51bc318`|F017,F046|no|M106,M297,M302,M308,M326,M503|F mul|field|
|F017 `M31::mul`|`crates/aspis-core/src/field.rs:133`|`0f4152a87fd44407044fd55aba805a7c2c70e942fae8af5d69c413847849589a`|F045|no|M077,M169,M201,M227,M298,M303,M309,M327,M356,M372,M415,M504|F reduce_u64|field|
|F018 `M31::neg`|`crates/aspis-core/src/field.rs:122`|`6bed68d8b1b11132210bde31846032cadb4ba5603ca1b32f9b51c780b373bb19`||no|M202,M304,M310,M328|none|field|
|F019 `M31::reduce_u62`|`crates/aspis-core/src/field.rs:145`|`ce2d69dff464ccd9362450e76514392c1f8fbf2f0381096f1669eb62e143f005`|F045|no|M203,M416|F reduce_u64|field|
|F020 `M31::reduce_u64`|`crates/aspis-core/src/field.rs:153`|`065261fab4e25c2593df2610ba9f3d47ff605780f8c233af825c7bced4ef9ed4`|F045|no|M050,M078,M170,M204,M228,M311,M329,M357,M373,M417,M495,M500|F reduce_u64|field|
|F021 `M31::sub`|`crates/aspis-core/src/field.rs:94`|`74df6dc4e93dba44f9318efe8774eae7571766ada6198334c2bc6d1c224be3d2`||no|M079,M171,M205,M229,M312,M330,M358,M374,M418|none|field|
|F022 `M31::to_le_bytes`|`crates/aspis-core/src/field.rs:248`|`0774e9f6386d6a3527957588a21ce51ea5f91734c5c90d169e60f94aa3bc2370`|F022|no|M240,M286,M349,M492|none|field|
|F023 `PreparedQm31Multiplier::new`|`crates/aspis-core/src/field.rs:448`|`e7596c6fcf0ea848f54445bb6cf54b3d8b718e3a865f04bd4325f00c7e0af793`|F001,F013,F024,F047|no|M206,M419|F add|field|
|F024 `QM31::add`|`crates/aspis-core/src/field.rs:896`|`59bab041e064fcd9a5ecb72a0aec1367770934b2eebf449fa47d0718266e366d`|F024|no|M080,M172,M207,M230,M331,M359,M375,M420|F add|field|
|F025 `QM31::from_cm31`|`crates/aspis-core/src/field.rs:891`|`58b9f162ff1ee7e5aca0f8906ff1f0b9bf471ab76933f50063c28c51cc672c51`||no|M342,M421|none|field|
|F026 `QM31::from_le_bytes`|`crates/aspis-core/src/field.rs:1022`|`a7672983e191fffb317d3b19a1212b34177048bd151d9ed41321db67038dc0e6`|F003|no|M021,M055,M096,M501|none|field|
|F027 `QM31::inv`|`crates/aspis-core/src/field.rs:1018`|`14a1ec0274f93cd698a9c9b7eb7315dbf9e8fd96abb38253d1e55ab8a123f934`|F034|no|no cohort counterpart|none|field|
|F028 `QM31::is_zero`|`crates/aspis-core/src/field.rs:985`|`a935b50299828040dbc802047ae32d1880c11150e70f3486dbca790d9f87ac1e`|F028|no|M332|none|field|
|F029 `QM31::mul`|`crates/aspis-core/src/field.rs:935`|`13e3e9d9c7b115eeae7fe9d8672f42a7cfb3e027d872a7b34d0d0d2f77926568`|F024,F029,F033,F035|no|M081,M173,M208,M231,M333,M360,M376,M422|F add,mul,sub|field|
|F030 `QM31::mul_m31`|`crates/aspis-core/src/field.rs:975`|`a3bc3300486bbfb743e7b831a688fe20ccb8d6885172f9fd9df4a2cf0e396d1f`|F030|no|M082,M209,M377,M423|F mul_m31|field|
|F031 `QM31::neg`|`crates/aspis-core/src/field.rs:916`|`6193946746119c5a83f1135945f395ee7ed456d697c17ffe7fa38d0107d8ba29`|F031|no|no cohort counterpart|F neg|field|
|F032 `QM31::square`|`crates/aspis-core/src/field.rs:951`|`d753e1472146cfa17f501d737426b4dd5342436ad7af400e8da2a853037f1cac`|F002,F014,F024,F029,F032,F035|no|M210,M334,M378,M424|F add,double,mul,square|field|
|F033 `QM31::sub`|`crates/aspis-core/src/field.rs:906`|`2f99fb3843d2f2f61391181cfb05232735408c0e603cdf612e1064c2cda6e44a`|F033|no|M083,M091,M211,M335,M361,M379,M425|F sub|field|
|F034 `QM31::try_inv`|`crates/aspis-core/src/field.rs:1004`|`1d4a03f4fd8ab36049bbbcdf033c09ff9c7303842bfa6cd91763c9732adb3c1e`|F027,F028,F029,F031,F032,F033,F035|no|M336|F inv,mul,neg,square,sub|field|
|F035 `mul_by_r`|`crates/aspis-core/src/field.rs:860`|`c8a29d8546ae41b4a149920d16db90e9aafc0dba7a55a5e997f9ec5e9646d0ff`|F001,F002,F012,F013,F014,F021,F024,F033,F047,F057|no|M084,M174,M212,M232,M337,M362,M380,M426|F add,double,sub|field|
|F036 `qm31_accumulate_product_channels`|`crates/aspis-core/src/field.rs:507`|`8d4b003e17b83b41cb61fa8c2854674b6a86c161c64b09c69b6e4df81de4a1b4`|F001,F013,F024,F047|no|no cohort counterpart|Loop 524,525; F add|field|
|F037 `qm31_from_karatsuba_channel_sums`|`crates/aspis-core/src/field.rs:481`|`89a73a65a1e79b97256f34f68d849e0921f8ba16631ca22980ec28106260ebbe`|F001,F012,F013,F020,F021,F024,F033,F035,F047,F057|no|M109,M427|F M31::reduce_u64,add,sub|field|
|F038 `qm31_m31_dot`|`crates/aspis-core/src/field.rs:1447`|`5c78eae051087191c4c7b1577de2ce23da7928c867ef5be2939791575e95945e`|F010,F020|no|M428|Loop 1456,1471,1474,1482; F M31::reduce_u64|field|
|F039 `qm31_pack_base4`|`crates/aspis-core/src/field.rs:1048`|`ff8c507c6aa8fd79022205f3c23362aefd4366837ab6e2a30ecfab0bc5aff146`|F010,F020|no|M429|F M31::reduce_u64|field|
|F040 `qm31_sum_products2`|`crates/aspis-core/src/field.rs:595`|`c0502ea9fb95e19bb038027292097d410822a0b1eef5b374248c1afdb7fafe70`|F044|no|no cohort counterpart|none|field|
|F041 `qm31_sum_products3`|`crates/aspis-core/src/field.rs:601`|`c0502ea9fb95e19bb038027292097d410822a0b1eef5b374248c1afdb7fafe70`|F044|no|no cohort counterpart|none|field|
|F042 `qm31_sum_products3_prepared`|`crates/aspis-core/src/field.rs:678`|`b8c6e6d6c66cdf471d1f66702241cfc0eee0893663975bb8f728b4538f14efea`|F001,F013,F024,F037,F047|no|M110,M430|Loop 680,695,696; F add|field|
|F043 `qm31_sum_products4`|`crates/aspis-core/src/field.rs:631`|`c0502ea9fb95e19bb038027292097d410822a0b1eef5b374248c1afdb7fafe70`|F044|no|no cohort counterpart|none|field|
|F044 `qm31_sum_products_small`|`crates/aspis-core/src/field.rs:534`|`b3ddf78a3a35d987f430c354e7d126c4277fd97a89d654cdcbcaa62921663c80`|F036,F037|no|no cohort counterpart|Loop 539|field|
|F045 `reduce_u64`|`crates/aspis-core/src/field.rs:31`|`ea04e7311160208e97026b9dc343b3b3bffae79735722e5bccd90d661ab0ef45`||no|M050,M051,M078,M085,M170,M175,M204,M213,M228,M233,M299,M305,M311,M313,M329,M338,M357,M363,M373,M381,M417,M431,M495,M496,M500,M502,M505|none|field|
|F046 `square_n`|`crates/aspis-core/src/field.rs:47`|`703cca2650daf476a656ca807834a2f14aec3cef27696c32e29bbf62c570a8e3`|F007,F017,F029,F051|no|M107,M300,M306,M314,M339,M506|Loop 48; F mul|field|
|F047 `WideExact::add`|`crates/aspis-core/src/field/wide_exact.rs:81`|`e4080f883505347da01570c80f3279502cfbbc7062760f985a34437bef1bd6bb`|F047|no|M067,M086,M382|F add|field|
|F048 `WideExact::from_le_bytes`|`crates/aspis-core/src/field/wide_exact.rs:255`|`be85509c9fdb54b33ef38278ec392165a9367cc5392aaad84f7cdacb451f2058`|F049|no|M056,M118,M186,M383|none|field|
|F049 `WideExact::from_limbs`|`crates/aspis-core/src/field/wide_exact.rs:207`|`06e57d0dfbbd626fa98d79d2d0948690302173d64a9f88f830873b398e0f2dd2`||no|M103,M119,M187,M384,M493|none|field|
|F050 `WideExact::from_qm31`|`crates/aspis-core/src/field/wide_exact.rs:73`|`d47e1e6cf34bb75cfe4bbcde90935288ae78577e8568ed985fb38b5fdc875a6b`|F060|no|M014,M343|none|field|
|F051 `WideExact::mul`|`crates/aspis-core/src/field/wide_exact.rs:112`|`6a8baeea9d7670a6a31622e6b977fe2eecb4450cb918d2ddfa1ec87f6a23a523`|F047,F051,F057,F061|no|M068,M087,M092,M105,M385|F add,mul,sub|field|
|F052 `WideExact::mul_m31`|`crates/aspis-core/src/field/wide_exact.rs:190`|`7ec95ba5b6a4408e97ae6b6b4ece79615df32dddc52903f8fcd225b0eef84264`|F052|no|M088,M386|F mul_m31|field|
|F053 `WideExact::mul_qm31`|`crates/aspis-core/src/field/wide_exact.rs:178`|`adcd6948269372db264b769b7c8078b0aa5d58aa79cc56477382cb55cb3c7679`|F051,F060|no|M387|F mul|field|
|F054 `WideExact::neg`|`crates/aspis-core/src/field/wide_exact.rs:101`|`e295f2a40803745151e143b209e86b4b568948bb4658fde6b3290d37033eb96f`|F054|no|no cohort counterpart|F neg|field|
|F055 `WideExact::new`|`crates/aspis-core/src/field/wide_exact.rs:55`|`771a650cf44a5a33a6607cd26d8c5e9b4c997562219c167d95f4aaa6bafe7d06`|F060|no|M112|none|field|
|F056 `WideExact::square`|`crates/aspis-core/src/field/wide_exact.rs:139`|`8c8c9697da2ebf487dd88dac2a53252e345cf033a819b3f357573ad17ca8a754`|F047,F051,F056,F061|no|no cohort counterpart|F add,mul,square|field|
|F057 `WideExact::sub`|`crates/aspis-core/src/field/wide_exact.rs:91`|`7de92babd43589c41f91412828da6305d0e610f6142c91e6e4beb333767fbadc`|F057|no|M089|F sub|field|
|F058 `WideExact::to_le_bytes`|`crates/aspis-core/src/field/wide_exact.rs:273`|`a952fa880bec4ea109c2be042cfb3a8c9f8f45a2a34fe9711f5a88f340bd726e`|F058,F059|no|M282,M284,M507|Loop 275; I|field|
|F059 `WideExact::to_limbs`|`crates/aspis-core/src/field/wide_exact.rs:238`|`3e648b095b6939fdb3b504c416d3e33617ee4d49c5fd3de545d22e1d531a488a`||no|M283,M285,M388,M494|none|field|
|F060 `canonical_qm31`|`crates/aspis-core/src/field/wide_exact.rs:283`|`7e334133a1dc749f6fee9738bb8147fb26dcba024df66e8b2d334906c2dcce82`||no|M015,M344,M389|none|field|
|F061 `mul_u`|`crates/aspis-core/src/field/wide_exact.rs:299`|`18f006ff837fa0d0023421523862b6a343484b12a0304ed3552d220b173e4461`|F035|no|M090,M093,M390|none|field|
|F062 `FibreIndex::get`|`crates/aspis-core/src/r0/domain.rs:18`|`a47676cbcdb365c2cd082e22ec6a5aea529168964134535a6e44910b772629f6`||no|M181|none|geometry|
|F063 `FibreIndex::new`|`crates/aspis-core/src/r0/domain.rs:11`|`0e79aae457fa92e9cc89046d3d495608c1152f524d3fa895bcebf72ecfc45c4f`||no|no cohort counterpart|none|geometry|
|F064 `filled`|`crates/aspis-core/src/r0/heap.rs:5`|`872b27756836699648c39573ecc257ed93235c523516f863c313dcb523527dbf`||no|M060,M391|none|alloc|
|F065 `parent_with_digest`|`crates/aspis-core/src/r0/merkle.rs:28`|`4ab7b85f08e1f3bb587e32016edc6d56994fc11650cd12bac1462077e19990bd`|F327|no|no cohort counterpart|O hash.digest|multiproof|
|F066 `QueryScan::finish`|`crates/aspis-core/src/r0_transcript.rs:216`|`7b5ee7968f5cfa93ce37def5be42d387dd49088e6f3120d2b40554714e98aaad`||no|M180|none|opening-transcript|
|F067 `QueryScan::scan`|`crates/aspis-core/src/r0_transcript.rs:202`|`69dbfce0fa1533d8cec2b12cb630f176a8c36e964ca44359ec477e8f48a06845`|F070|no|no cohort counterpart|Loop 203; B |opening-transcript|
|F068 `block_rank`|`crates/aspis-core/src/r0_transcript.rs:89`|`49ec5dd4d45ad00fbe1da699a9dbdcd9b838bada1b5fe26ac5a1a04388464cc9`||no|M184|none|opening-transcript|
|F069 `queries_from_pairs`|`crates/aspis-core/src/r0_transcript.rs:305`|`b9bef69c7987a399320d3ff7735a4a305dd4c642f27b15d5c0e06906156732ac`|F066,F067,F202|no|no cohort counterpart|Loop 311|opening-transcript|
|F070 `query_words`|`crates/aspis-core/src/r0_transcript.rs:186`|`6e2dce93efe510cfffa10acc7674eb6e2412cc42362d922549eb14cab10517de`|F068|no|M185|I; O block_rank(block).map|opening-transcript|
|F071 `cm31_mul_i`|`crates/aspis-core/src/state_only_hiding.rs:437`|`0b912f8c12f8842a7703301579b278eff0af1cab9adb73b896cc7a92c9dbf039`|F009,F010,F018,F031,F054|no|M214|F neg|semantic-eval|
|F072 `cm31_mul_r`|`crates/aspis-core/src/state_only_hiding.rs:442`|`3ae03ba9c0f810772b94a6e3dd9bab0ca04cbd2f70db989e23f4163dd309f71e`|F001,F002,F010,F012,F013,F014,F021,F024,F033,F047,F057|no|M215|F add,double,sub|semantic-eval|
|F073 `mask_power_26`|`crates/aspis-core/src/state_only_hiding.rs:520`|`8e4bbb4d43d2059abe4596e9f811e57ef25c8cd4f96b3e26e0336d6b38645564`|F007,F011,F017,F029,F032,F051,F056|no|M216|F mul,square|semantic-eval|
|F074 `mul_tower_basis`|`crates/aspis-core/src/state_only_hiding.rs:448`|`f4a1e58384ccc422b360fa0eca9632a5233fc4211acf52b8e3cdfe8735ba9dd6`|F071,F072|no|M217|none|semantic-eval|
|F075 `selected_mask_linears`|`crates/aspis-core/src/state_only_hiding.rs:499`|`b9d38a235f63faf530332ebc379dd898ca9713cee634d7965d6b94cfbdb30e2f`|F001,F008,F013,F024,F030,F047,F052|no|M218|Loop 502; I; F add,mul_m31|semantic-eval|
|F076 `state_only_selected_mask_value`|`crates/aspis-core/src/state_only_hiding.rs:647`|`bc58569304404babe325e124d2a74817364b7b68eb9f33b786c84ba1d00f77c4`|F001,F007,F013,F017,F023,F024,F029,F047,F051,F073,F074,F075|no|M219|Loop 655,659,666; I; F add,mul|semantic-eval|
|F077 `private_leaf_hash_with_digest`|`crates/aspis-core/src/state_only_private_merkle.rs:40`|`13bc91af598ba8984ba3400e13461d4494e4432867461732633d4115eb11b782`|F327|no|no cohort counterpart|O hash.digest|multiproof|
|F078 `batch_key_at`|`crates/aspis-r1-cost-probe/src/candidate.rs:148`|`9375a4d3a90b700556a0791c63a09028877e7efc3a498a5e5ae80caa95186391`||no|no cohort counterpart|none|keys|
|F079 `batch_keys`|`crates/aspis-r1-cost-probe/src/candidate.rs:92`|`9184bd058bf5b12f9e29468332ccc284553ead3e1165c6e8f39967ba49173174`||no|M038|Loop 94|keys|
|F080 `batch_leaf`|`crates/aspis-r1-cost-probe/src/candidate.rs:117`|`7e28698baab02eff1799ae0e2bb6c1b2465126f533f12dd2c1a19ee79745439f`|F077|no|M039|O private_leaf_hash_with_digest|keys|
|F081 `batch_merkle`|`crates/aspis-r1-cost-probe/src/candidate.rs:156`|`5d3185fb3c312df117d4ac648233fa5058c852938374a192811445e2c255559d`|F082|no|M028|none|batch|
|F082 `batch_merkle_values`|`crates/aspis-r1-cost-probe/src/candidate.rs:162`|`f09046e56911e28a71281efdd6d4ff94c2e83bc9d603bba8904e41e130e61936`|F083|no|M029|B 166,166,167,167,168,168|batch|
|F083 `batch_tree`|`crates/aspis-r1-cost-probe/src/candidate.rs:173`|`3feed1a7f0bdd8ea5089b0bc974fe5d61bb041e0c24d378ac6e40e4fd6a35342`|F078,F079,F080,F085,F090,F091,F092,F093,F122,F127|no|M030|Loop 180; I; B |batch|
|F084 `canonical_scan`|`crates/aspis-r1-cost-probe/src/candidate.rs:54`|`66bbf3452338ab0aa3d5f779c55c38f84a0ff42261abc69d199d10dd18cd61d0`|F015,F026,F085,F096,F189|no|M490|Loop 59,61,62,66|shape|
|F085 `opening`|`crates/aspis-r1-cost-probe/src/candidate.rs:29`|`028b69f947f492303bf8a3c39d6173b877833d4f19f7e3fcd7cade0a287a364a`||no|M040|none|keys|
|F086 `parse_shape`|`crates/aspis-r1-cost-probe/src/candidate.rs:40`|`41d660ce759042d8296dd5122654b5af6b1897a98ecc8f5a2d79630760b2a4fe`|F173|no|M489|I|shape|
|F087 `prepare`|`crates/aspis-r1-cost-probe/src/candidate.rs:255`|`3056a22866e0fe1e3b4330800cee6d284b272928bd3ddf8dbec592c8fb8ee1e6`|F064,F095,F098,F099,F137,F179,F191|no|M063|B |prepare|
|F088 `query_loop`|`crates/aspis-r1-cost-probe/src/candidate.rs:239`|`db07a00554acb64ff91b1e5ccf587feba5db14deb337efc4a5fb47ef11d991fe`|F089|no|M034,M236|Loop 241|query|
|F089 `query_values`|`crates/aspis-r1-cost-probe/src/candidate.rs:212`|`ab4b8881aeeec9bf90292d284bbe0db76e3be77f8f8f9473720af6188dafa680`|F002,F007,F012,F014,F017,F021,F029,F033,F051,F057,F085,F104,F164,F180,F182,F188,F190,F191,F196|no|M035|B 232,232; F double,mul,sub|query|
|F090 `same_batch_index`|`crates/aspis-r1-cost-probe/src/candidate.rs:142`|`58f76e0bd7f39fed3b37325b66e88522992873f4aebfa08d35220d83dcceed58`||no|M024|none|keys|
|F091 `same_batch_leaf`|`crates/aspis-r1-cost-probe/src/candidate.rs:136`|`ab9ddbf6e34161f92525212249859d894b23d9574f009855e1bdac992a44f9f8`||no|M025|none|keys|
|F092 `slot`|`crates/aspis-r1-cost-probe/src/candidate.rs:34`|`fc2fcc8a5aa52bdb44b9b379c8274a7847de79859cad3f7902edcde05a2f39a5`|F100|no|M041|none|keys|
|F093 `sort_batch_keys`|`crates/aspis-r1-cost-probe/src/candidate.rs:104`|`cff533add02fd02df332860e6d81c3dccd32783b5757a2967b75de797938a04d`|F078|no|M043|Loop 105,107|keys|
|F094 `tx1`|`crates/aspis-r1-cost-probe/src/candidate.rs:270`|`e7cd5d10bd41d9d5666e5d07464d52b0cb1fd333e987dae8522bdb543bd6b79a`|F081,F084,F086,F087,F088,F174,F175,F176,F181,F186,F191|no|M064|B 278,287|driver|
|F095 `wide_view`|`crates/aspis-r1-cost-probe/src/candidate.rs:76`|`42d59d74d96c715a865bec8e75b838893f2ab12c0167735fa5d5b5adbf8a29a1`|F048|yes|M221|none|leaf:wide_view|
|F096 `check_values`|`crates/aspis-r1-cost-probe/src/compact.rs:139`|`05d7393a7534db22a95fec75a06dd1349fb4c426999973a6c157c01c11ccfeee`|F026|yes|M487,M491|Loop 140; I|leaf:check_values|
|F097 `compact_row`|`crates/aspis-r1-cost-probe/src/compact.rs:80`|`6ddfd226b135d3e070000576db8ddbaf8ea1573d37bdbf38911f917d4f60c94c`||no|M345|none|parser|
|F098 `expand_semantic`|`crates/aspis-r1-cost-probe/src/compact.rs:148`|`2f05c2a6fb17a8e59287a923c9b3fcef4a0f651bce48a92b9fbb7303c79f7b94`|F097,F099,F153|no|M346|Loop 154; B 160|parser|
|F099 `expand_values`|`crates/aspis-r1-cost-probe/src/compact.rs:127`|`86ca9cc0fc0a21eca47b232873e3f171de50713ff931cb63b0716bee2863a324`||yes|no cohort counterpart|Loop 131; I; B |leaf:expand_values|
|F100 `slot_offset`|`crates/aspis-r1-cost-probe/src/compact.rs:56`|`750c2f21faaf31375404d57dcf2f2e2a197e8920fe8b7568cc53d9b90e9846c4`||no|M042|Loop 59|parser|
|F101 `fibre_point`|`crates/aspis-r1-cost-probe/src/fast_domain.rs:282`|`c44323f146aac19db295b187edce0a5bc09ee6cdd49e7aae04f274e77b3b1b79`|F007,F017,F029,F051,F062,F103|no|M182|F mul|geometry|
|F102 `line_node`|`crates/aspis-r1-cost-probe/src/fast_domain.rs:295`|`0c00e1cf5b320426d49b2996e6e42ada97423e4e5b34abc82737acabe8893a54`|F002,F007,F012,F014,F017,F021,F029,F033,F051,F057,F101|no|no cohort counterpart|F double,mul,sub|geometry|
|F103 `table_value`|`crates/aspis-r1-cost-probe/src/fast_domain.rs:276`|`fb2fb3b9ea1058d87f135f456df562d8c65538fd929da6378b14ac2cad4c25f3`|F010|no|M183|none|geometry|
|F104 `four_dots`|`crates/aspis-r1-cost-probe/src/fast_dots.rs:67`|`c3841f0a0f2ea0242f9f5a507c0e2a5cdd925bc30df8d8c2f920e2d4286bebce`|F105|no|M022|none|dots|
|F105 `four_dots_one`|`crates/aspis-r1-cost-probe/src/fast_dots.rs:15`|`6061bc500d2f2d1600817960f709af5c5d0a1dc3585fa9d62fa9066ff84c8d11`|F001,F013,F015,F020,F024,F026,F047,F049,F059,F106,F107,F108|no|M023|Loop 17,19; F M31::reduce_u64,add,unwrap|dots|
|F106 `EbyKDot::finish`|`crates/aspis-r1-cost-probe/src/fast_pairing.rs:176`|`887e378cc8c8a8c8267e56b7b66477a5e7a9000a91c8cfab47057a50da40ae56`|F049,F109,F114|no|M099,M392|none|dots|
|F107 `EbyKDot::new`|`crates/aspis-r1-cost-probe/src/fast_pairing.rs:160`|`a0fbee47b56e74fd7190d88d11dc38cd38bfa356c48f7361e42de14d1bd9f7b2`|F110|no|M237,M393|none|dots|
|F108 `EbyKDot::push`|`crates/aspis-r1-cost-probe/src/fast_pairing.rs:165`|`0a69f40fecb6fa1a3e661c695929992da16636379f1534e0ccb14bafe8f10395`|F111,F113,F116|no|M394|B |dots|
|F109 `canonical::Dot::finish`|`crates/aspis-r1-cost-probe/src/fast_pairing.rs:123`|`ee1535d1a977f8acee0e7e445421cc921e069c8994e07a529946ccfbecf74573`|F115|no|M057,M100,M395|none|dots|
|F110 `canonical::Dot::new`|`crates/aspis-r1-cost-probe/src/fast_pairing.rs:112`|`8d4cbc69049afad585a5c43f20231fbd0e8e4bce2528e53bf0961359ce8bb7e5`||no|M238,M396|none|dots|
|F111 `canonical::Dot::push`|`crates/aspis-r1-cost-probe/src/fast_pairing.rs:114`|`0690762c9d2c31673fed24b3cd4a34a41cd6383c4f53ff64079550dd817e420c`||yes|M098,M397|Loop 118; B |leaf:push:canonical::Dot|
|F112 `canonical::Q::from_limbs`|`crates/aspis-r1-cost-probe/src/fast_pairing.rs:24`|`5f66448bfb31976fa7c30fa23e04a61e13865bb1628fe4d6fedb56ca7bdebc23`||no|M398|none|dots|
|F113 `canonical::Q::from_wide`|`crates/aspis-r1-cost-probe/src/fast_pairing.rs:33`|`54c2900b8009e0413c553c3412a5b2386981493156b496717fd6e42579b14cbb`|F059|no|M399|none|dots|
|F114 `canonical::Q::limbs`|`crates/aspis-r1-cost-probe/src/fast_pairing.rs:29`|`294ecea20b56a78b8af6286113bae45eeeb445a16b7f90fceb163cba8ec98bab`||no|M101,M400|none|dots|
|F115 `canonical::reduce`|`crates/aspis-r1-cost-probe/src/fast_pairing.rs:10`|`33b2e64d82b52ace1b69f3d5bc6f711cbcfa45e2b5737f035876ec5b15dc9823`||no|M058,M102,M401|none|dots|
|F116 `checked_q`|`crates/aspis-r1-cost-probe/src/fast_pairing.rs:138`|`fd14f9f66985884db8e11b71ba8f36db0a14f6847e5e8a68fce19351098e45db`|F112,F117|no|M402|none|dots|
|F117 `limbs_of`|`crates/aspis-r1-cost-probe/src/fast_pairing.rs:133`|`1b17bd83e597c464125ba785a67ddecd5499113369a300be51ab184889289dd1`||no|M403|none|dots|
|F118 `Arity::bits`|`crates/aspis-r1-cost-probe/src/multiproof.rs:32`|`546a480c2596f8e9ed19c455aaeaadf0140c9e2b4edf4a3c853d3757178c7010`||no|no cohort counterpart|none|multiproof|
|F119 `Arity::levels`|`crates/aspis-r1-cost-probe/src/multiproof.rs:43`|`c930a78a1df8a23cf99e48e2bf88eb1449453f4c9f0588a0ea99ba53b09583e3`|F118|no|no cohort counterpart|none|multiproof|
|F120 `Arity::width`|`crates/aspis-r1-cost-probe/src/multiproof.rs:39`|`4cb585a215a0dface45ee399077ff62b3fad5aec8ea5c93e0f24a2ef5671b14c`|F118|no|no cohort counterpart|none|multiproof|
|F121 `index_at`|`crates/aspis-r1-cost-probe/src/multiproof.rs:62`|`fb50c5eb22c58411bca20dff8dc5854399b405e88591982a0525c1e214c2ae4e`||no|no cohort counterpart|none|multiproof|
|F122 `node_count`|`crates/aspis-r1-cost-probe/src/multiproof.rs:85`|`19c689b177eaa992ec60264993d47d5880fe5d07ad77b12c682ff7a8c528967e`|F118,F119,F120,F121,F128|no|M037|Loop 93,96,99|multiproof|
|F123 `occupied_binary_parent`|`crates/aspis-r1-cost-probe/src/multiproof.rs:73`|`9682d654cd2640087b4b06be05503cb2f9a8ab282fdebe0d70621b976482da39`|F327|no|no cohort counterpart|O hash.digest|multiproof|
|F124 `root_matches`|`crates/aspis-r1-cost-probe/src/multiproof.rs:70`|`c879f9d0a00520505a521c6e186888ca23d1f2fccbe63bb1bdefe9f468876e35`||no|no cohort counterpart|none|multiproof|
|F125 `sibling_binary_parent`|`crates/aspis-r1-cost-probe/src/multiproof.rs:78`|`ce4a228046a9684d22a6572edd7253118eb5631c05d39fe59b10db1b571a907c`|F327|no|no cohort counterpart|O hash.digest|multiproof|
|F126 `value_at`|`crates/aspis-r1-cost-probe/src/multiproof.rs:67`|`4574347385146c0b5a87239076136f997176576f5c9b0d30e82de1e1d74c43be`||no|no cohort counterpart|none|multiproof|
|F127 `verify_in_place`|`crates/aspis-r1-cost-probe/src/multiproof.rs:138`|`cc8c08dc90a3b055e66141f3e0d9b67ba3df8fd7ea2f55e031e4bbe13d718c63`|F065,F118,F119,F121,F123,F124,F125,F126,F128|no|M044|Loop 151,154,174; I; B ; O merkle::parent_with_digest|multiproof|
|F128 `well_formed`|`crates/aspis-r1-cost-probe/src/multiproof.rs:54`|`9e2022011570854c66e81e8eb3a4f80df19ef43ee17011aeb90ef99cfd89d06f`||no|no cohort counterpart|I|multiproof|
|F129 `claims`|`crates/aspis-r1-cost-probe/src/r1_semantic.rs:42`|`2c15185f5c5674b38b2795893456728e2b67d3a353eaffcb53e0909e34518e92`|F001,F013,F024,F047,F141,F147|yes|M061|Loop 47; F add,write|leaf:claims|
|F130 `mark`|`crates/aspis-r1-cost-probe/src/r1_semantic.rs:75`|`695c8fef4adcded6138e95d6552323008bdc221ddaa1af8f0445a50f4507fdb4`||no|no cohort counterpart|none|control|
|F131 `public_transcript`|`crates/aspis-r1-cost-probe/src/r1_semantic.rs:63`|`d2e96e15a5eff12832937c6574b0d279dfc1e7672756bcd5bd1c313815055d4f`|F143,F254|no|M139|none|semantic-transcript|
|F132 `semantic_boundary`|`crates/aspis-r1-cost-probe/src/r1_semantic.rs:82`|`41398f73e3ad9ace184bf2d2f5b88d32ea07eac836a068dee78dd03dc38d8851`|F024|yes|M234|I|leaf:semantic_boundary|
|F133 `semantic_round`|`crates/aspis-r1-cost-probe/src/r1_semantic.rs:96`|`d97fe825c12185406af18fe9371bbc471618d18040757b26be53bc4cfccd04ab`|F132,F135,F141,F145,F147|no|no cohort counterpart|none|semantic-transcript|
|F134 `semantic_rounds`|`crates/aspis-r1-cost-probe/src/r1_semantic.rs:133`|`c199d097ccfbba89f680d60cc1b4443471d880c774d60dff079faf85ffb96e5d`|F133,F141,F147|no|no cohort counterpart|none|semantic-transcript|
|F135 `semantic_value`|`crates/aspis-r1-cost-probe/src/r1_semantic.rs:87`|`4bac80fd56049348890dd43f156010a80ceda3b5d9803070665679b23687677d`|F001,F007,F013,F017,F024,F029,F047,F051|no|M235|I; F add,mul|semantic-transcript|
|F136 `verify_finish`|`crates/aspis-r1-cost-probe/src/r1_semantic.rs:232`|`f18e1c9bd12e9e9d2cd19e63163ae6ed5b4c03beae34f21e4ccb6c2fd81339f6`|F001,F007,F013,F017,F024,F029,F047,F051,F076,F129,F130,F134,F139,F141,F142,F146,F147,F256|no|M126|F add,mul|semantic-transcript|
|F137 `verify_observed`|`crates/aspis-r1-cost-probe/src/r1_semantic.rs:311`|`9d1080554ec5a6a8097eeb9f2450509a2f1e2583a6422cb35462013b904120d5`|F130,F131,F136,F138,F150|no|M131|B 315|semantic-transcript|
|F138 `Prefix<'a>::parse`|`crates/aspis-r1-cost-probe/src/r1_wire.rs:292`|`632a4cb5b3039078835d0a4d248e2e1c51cfa010b447d1b2e4fe5d81385211f9`|F152|no|M120|none|parser|
|F139 `Prefix<'a>::payload`|`crates/aspis-r1-cost-probe/src/r1_wire.rs:344`|`2bc1d52e43bdef100a0aa5e3428aab5a31ffdc47de3f1500ec599fbb54c55a56`|F140|no|no cohort counterpart|none|parser|
|F140 `Prefix<'a>::record`|`crates/aspis-r1-cost-probe/src/r1_wire.rs:338`|`ae2f154f959c5ab6c211b45e5d30a30c5661fd3faf8c1d6780fdffce99055678`||no|M140|none|parser|
|F141 `Prefix<'a>::validated_record`|`crates/aspis-r1-cost-probe/src/r1_wire.rs:348`|`79818500ecbfe3535437ade1c0198359c67883b3f77c83f5530d1252e02e7a21`|F140|no|M141|none|parser|
|F142 `SemanticTranscript<H>::circle_validated`|`crates/aspis-r1-cost-probe/src/r1_wire.rs:233`|`deb91b76bb02c29f6358241b6c38049a3f926e91e97431fdf35c0713a7bff31f`|F144,F148,F149,F156|no|M125|B |semantic-transcript|
|F143 `SemanticTranscript<H>::new`|`crates/aspis-r1-cost-probe/src/r1_wire.rs:179`|`ab3b12d14824021f528d01c0a3e86a2cd845d79d9051ee8054f133fa80e5427b`|F022,F058,F327|no|M143|O hash.digest|semantic-transcript|
|F144 `SemanticTranscript<H>::sample_block_validated`|`crates/aspis-r1-cost-probe/src/r1_wire.rs:194`|`587a232d442b8568fa091f0410069b9db5143ba8d00999c95795220de0944186`|F327|no|M144|B ; O self.hash.digest|semantic-transcript|
|F145 `SemanticTranscript<H>::semantic_validated`|`crates/aspis-r1-cost-probe/src/r1_wire.rs:220`|`fa4695cd46f2ad809a542ead438d09c4ebeede4b6aae3759435c0ced1fd36f2f`|F144,F148,F149,F163|no|M145|B |semantic-transcript|
|F146 `SemanticTranscript<H>::state`|`crates/aspis-r1-cost-probe/src/r1_wire.rs:187`|`d1c1813cc0e421d02d802cbd4e258b81af2aa65598e3e65bb4fad3f911b12369`||no|M142|none|semantic-transcript|
|F147 `ValidatedRecord<'a>::decode_k`|`crates/aspis-r1-cost-probe/src/r1_wire.rs:139`|`704a7d5187067262751366a7dc55b5822aee48bf19405f202ec9ac4bdd7b2fc2`|F026|yes|M097|Loop 158; I|leaf:decode_k:ValidatedRecord<'a>|
|F148 `ValidatedRecord<'a>::framed`|`crates/aspis-r1-cost-probe/src/r1_wire.rs:127`|`26c096cad2f19009b659038087d57837f1d9d854867a37d974e10a9a5c4bbd87`||no|M146|none|parser|
|F149 `ValidatedRecord<'a>::row`|`crates/aspis-r1-cost-probe/src/r1_wire.rs:123`|`bca2db81f1174a866bd3aafde41ab0d95cc9775880ab6a372dc91c9d5285602d`||no|M147|none|parser|
|F150 `begin`|`crates/aspis-r1-cost-probe/src/r1_wire.rs:390`|`eba1b5319a510007dff78d1e664cf5459bf7c0f5423a17eae6323038f4e5c109`|F141,F145|no|M148|B |semantic-transcript|
|F151 `parse_record`|`crates/aspis-r1-cost-probe/src/r1_wire.rs:63`|`710d2341cdd876ef93086aa152225d7f235b2cae6661d589c1bea7302514bd19`|F153,F154|no|M121,M188|none|parser|
|F152 `parse_record_at`|`crates/aspis-r1-cost-probe/src/r1_wire.rs:278`|`4af3721c9609eea724ac4c8f32efddb643d0f5b0007f942ea31f3a647400be4c`|F151,F153|no|M122|none|parser|
|F153 `row_shape`|`crates/aspis-r1-cost-probe/src/r1_wire.rs:39`|`be7035e6a6289a1b7b592026ee425ab9dfd1308035a34e2b768de0513d05e0c0`||no|M123,M189,M191,M347|none|parser|
|F154 `validate_record_fields`|`crates/aspis-r1-cost-probe/src/r1_wire.rs:51`|`44097d81290ba71420bd4ac302f4fff11d7095de31d8f4621e7fc9b484635757`|F048|yes|M124,M190|Loop 52; I|leaf:validate_record_fields|
|F155 `add_small_base_p`|`crates/aspis-r1-cost-probe/src/sampler.rs:90`|`f49fe730c068cc39fd5c513f601fe3ad2d9a86e4277b0f3d57f0895c08a56938`||no|M117|Loop 91; B |sampler|
|F156 `circle_sample`|`crates/aspis-r1-cost-probe/src/sampler.rs:121`|`2c7ae667ed96e6f7b6e2bd0abe192faf9f7ac7c3fc6d9a19d3f5fb3c54fadffa`|F163|yes|M059|O secure_ood_circle_point_from_parameter(qm31_sample(block)).unwrap_or_else|leaf:circle_sample|
|F157 `decode8`|`crates/aspis-r1-cost-probe/src/sampler.rs:75`|`ab3ab37dae8d56421e76583e6ff103e21d6fcf9ac8aebb2c93bb4615c3db5080`|F010,F055|no|M113|none|sampler|
|F158 `gamma_sample`|`crates/aspis-r1-cost-probe/src/sampler.rs:111`|`a59d9b159a08f8d6a5f58f2590e272ef3aa92f79e64d06dc20af8b366e6cbedc`|F155,F157,F159|no|M104|B 113,115|sampler|
|F159 `low_base_p_digits`|`crates/aspis-r1-cost-probe/src/sampler.rs:56`|`3bb6e666c77f8662db27efe930fbdd071b8542828ce16fce2fd4eaee944a8c1b`||yes|M114|Loop 61; I; O block[4 * i..4 * i + 4].try_into,block[4 * i..4 * i + 4].try_into().unwrap|leaf:low_base_p_digits|
|F160 `ordinary_sample`|`crates/aspis-r1-cost-probe/src/sampler.rs:102`|`911c6ce3f4af81712181669376eda47cba7ec761a33e9b4780344996adb0667c`|F157,F159|no|M115|none|sampler|
|F161 `qm31_digits`|`crates/aspis-r1-cost-probe/src/sampler.rs:21`|`339f74077fe68f42bb14f517fa1fdcda95d940c46b6953caf546f48fb2e17fe0`|F162|no|M149,M177|Loop 24,36|sampler|
|F162 `qm31_div_pass`|`crates/aspis-r1-cost-probe/src/sampler.rs:8`|`e8930cee8562e90313c07c13eee12960e223c7b562e90bfd6541adc72f0e5cdd`||no|M116,M150,M178|Loop 11|sampler|
|F163 `qm31_sample`|`crates/aspis-r1-cost-probe/src/sampler.rs:45`|`fe03cd3319a9b98eace0975ceb0fc5e49c64867dfed339c65011a77593f61c55`|F010,F161|no|M151,M179|none|sampler|
|F164 `value`|`crates/aspis-r1-cost-probe/src/trace.rs:6`|`10e7cd0bed4a9659dc28bddff579217578b016047b2e8190457b6db53babedea`||no|M069,M152,M404|none|control|
|F165 `Transcript<H>::absorb`|`crates/aspis-r1-cost-probe/src/transcript.rs:14`|`3c19a014b8b7710c4489334e765652c49974fe02f08342ca7692932c52212344`|F022,F058,F327|no|M153|B ; O self.hash.digest|opening-transcript|
|F166 `Transcript<H>::block`|`crates/aspis-r1-cost-probe/src/transcript.rs:17`|`9d44a0291ad0151037c729a122bed3ca4f1369b8cfd44c43e4f7d9525558fc71`|F165,F327|no|M154|B ; O self.absorb,self.hash.digest|opening-transcript|
|F167 `Transcript<H>::new`|`crates/aspis-r1-cost-probe/src/transcript.rs:7`|`827d3e0fd1583ad96a320b8dff129d02e94c74f2374f4a532daca5303d4f8eeb`|F173,F327|no|M155|O hash.digest|opening-transcript|
|F168 `Transcript<H>::queries`|`crates/aspis-r1-cost-probe/src/transcript.rs:35`|`f6fe390c8be698805aa7a1b1db28219524b449a965f26e5efe5e171f78e07797`|F069,F164,F165,F327|no|M130|B ; O self.absorb,self.hash.digest|opening-transcript|
|F169 `Transcript<H>::scalar`|`crates/aspis-r1-cost-probe/src/transcript.rs:23`|`f9f39a2143df8d1600cfd4f72d35806e797b32f5aeb2f634bcc96628d949a48b`|F158,F160,F164,F166|no|M127|B ; O self.block|opening-transcript|
|F170 `Transcript<H>::scalar_k`|`crates/aspis-r1-cost-probe/src/transcript.rs:31`|`fd57c335f704bab7bad7cdae648d1822ab17da71555172839b47b07c4bbd0d4e`|F050,F163,F164,F166|no|M128|B ; O self.block|opening-transcript|
|F171 `Variant::final_len`|`crates/aspis-r1-cost-probe/src/transport.rs:9`|`cfda1436d0052e5c8701207708ffa1112805a78f8d318616f233c7a1c69b9b39`|F172|no|no cohort counterpart|none|control|
|F172 `Variant::folds`|`crates/aspis-r1-cost-probe/src/transport.rs:8`|`3dbedb2e6e1ed27a3a7e0901ec9b8b29be44cf40ed3641e9899bb561927004bd`||no|M156|none|control|
|F173 `Variant::tag`|`crates/aspis-r1-cost-probe/src/transport.rs:6`|`17ab5f97dc2e0940159c6ae5f9cc81828df106fe8b1e43c04806f74c25f1ec33`||no|M001,M157,M488|none|control|
|F174 `Accumulator::new`|`crates/aspis-r1-cost-probe/src/verifier.rs:93`|`6801d8eb675536ffd513dce58800ddbd9aa521657358a2e1ea0084e6d6456a7f`|F064,F171|no|M027|none|driver|
|F175 `BatchedWeights::finish`|`crates/aspis-r1-cost-probe/src/verifier.rs:226`|`0e63b316478638019c5ed83d0f4cdc8964f7dbf984bdd0c2cddc870da01df48a`|F178|no|M026,M497|Loop 226; I; B |residue|
|F176 `BatchedWeights::new`|`crates/aspis-r1-cost-probe/src/verifier.rs:206`|`2a5737a9366f6b2cfe9d4409668bde8247aa6bb63da99e130edb941fd38f345c`|F064|no|M032|Loop 209|residue|
|F177 `BatchedWeights::push`|`crates/aspis-r1-cost-probe/src/verifier.rs:217`|`6f0e38c5b3d0592b335cb62dc540a2748501bd47f2b8bda3e856985d13ed97f7`|F195|no|M036|B 219|residue|
|F178 `BatchedWeights::value`|`crates/aspis-r1-cost-probe/src/verifier.rs:222`|`71579a06f4ca55affc22aefa171bd4a1ede6c993bf484c71f061a0fe6e77d18e`|F020|no|M052|I|residue|
|F179 `Prepared::new`|`crates/aspis-r1-cost-probe/src/verifier.rs:72`|`0b181976b7d92675b134b32c3d00f87296e3aedf84efdf5e138a7bf28189cbae`|F022,F058,F146,F167,F168,F169,F170,F172,F193,F197|no|M129|B |opening-transcript|
|F180 `QueryGeometry::for_query`|`crates/aspis-r1-cost-probe/src/verifier.rs:179`|`585cf3766ded55b1585fd713f8b7501bb9d2fc43728b0336f5101d5c01309765`||no|no cohort counterpart|none|geometry|
|F181 `QueryGeometry::for_range`|`crates/aspis-r1-cost-probe/src/verifier.rs:148`|`cecda71c277c78a80c9dedd96c0148a2907410736135eeef24f3c1c0ffeaf154`|F002,F005,F007,F012,F014,F016,F017,F021,F027,F029,F033,F051,F057,F063,F101,F102,F185|no|M031|Loop 152,171; I; F double,inv,mul,sub|geometry|
|F182 `accumulate_batched_with_node`|`crates/aspis-r1-cost-probe/src/verifier.rs:277`|`4bb575a783c944b146f564b076a7cd1d3df4db7cce59a10f225e8eae12994afa`|F001,F002,F007,F012,F013,F014,F017,F021,F024,F029,F033,F047,F050,F051,F053,F057,F164,F177,F183,F184|no|M033|Loop 280,280,281; B ; F add,double,mul,mul_qm31,sub|accumulate|
|F183 `accumulated_weight_at`|`crates/aspis-r1-cost-probe/src/verifier.rs:274`|`9bae9bc0891859f088e0e1dca4c9e8db7e8b4a14d0c2fecb21a74a8e6ab459fd`||no|no cohort counterpart|none|accumulate|
|F184 `basis_at`|`crates/aspis-r1-cost-probe/src/verifier.rs:272`|`486bc40aa1bda4eb6488bea22dff0d7d5b3d474eeab3c8c9054af3d1d47bd998`||no|no cohort counterpart|none|accumulate|
|F185 `batch_prefix_products`|`crates/aspis-r1-cost-probe/src/verifier.rs:134`|`819dce1c5d717078e0b354f05139e44e402c5234dd5f3a8bd77df46996b6ec87`|F007,F017,F029,F051|no|M045|Loop 138; F mul|geometry|
|F186 `checkpoint`|`crates/aspis-r1-cost-probe/src/verifier.rs:326`|`4ca82e5e900b725be771f0b09faffdaf910d9cf414a08e49f1197a34ad0b0a6f`|F022,F058,F173,F187,F327|yes|M016,M017|Loop 330,331,333,334,335,335,336,338; B 331,332,334,335,336,337,338; O hash.digest|leaf:checkpoint|
|F187 `checkpoint_size`|`crates/aspis-r1-cost-probe/src/verifier.rs:32`|`71911778c085f5b728b5ed94340a528678e29a6cf704e8f8015a58cdb84de159`|F171|no|no cohort counterpart|none|wrapper|
|F188 `circle_fold_with_inverses`|`crates/aspis-r1-cost-probe/src/verifier.rs:182`|`f91cd9637267d713b0fe130c79ecab6c98400adfa2f388c18ce5f6f8c36caad4`|F001,F007,F008,F012,F013,F017,F021,F024,F029,F030,F033,F047,F051,F052,F057|no|no cohort counterpart|F add,mul,mul_m31,sub|query|
|F189 `echeck`|`crates/aspis-r1-cost-probe/src/verifier.rs:39`|`cb2dee116d269dd606d07a201d011ed4dcd38af204312d97f6f93616b8a544c1`|F048|yes|no cohort counterpart|Loop 40; I|leaf:echeck|
|F190 `line_fold_with_inverses`|`crates/aspis-r1-cost-probe/src/verifier.rs:191`|`61cb34a1e43fb6611f6e550bf27d397e0f874b13d7beec3f728a4679543ea34d`|F001,F007,F008,F012,F013,F017,F021,F024,F029,F030,F033,F047,F051,F052,F057|no|no cohort counterpart|F add,mul,mul_m31,sub|query|
|F191 `mark`|`crates/aspis-r1-cost-probe/src/verifier.rs:31`|`8d11b2880963463305373885b0ac2b54c695091dad56461a54b77bffd87775d3`||no|M065|none|control|
|F192 `power_limb_at`|`crates/aspis-r1-cost-probe/src/verifier.rs:233`|`d8534398dbd555cc81e530de0c7e3b454c79377cac62684f329b2bddb82bb1e9`||no|no cohort counterpart|none|residue|
|F193 `prepared_claim`|`crates/aspis-r1-cost-probe/src/verifier.rs:53`|`ad61cec1c8539b4cf738fc8cba61cf0bb48ca150083e92ce324f759e8653f922`|F001,F007,F013,F017,F024,F029,F047,F051,F106,F107,F108,F164,F196,F197|yes|M070|Loop 56,58,65; F add,mul|leaf:prepared_claim|
|F194 `residue_limb_at`|`crates/aspis-r1-cost-probe/src/verifier.rs:231`|`8127793a5379aaddb568da63252c5b92c7465d40b8cf8d8352a12672f87d54e3`||no|no cohort counterpart|none|residue|
|F195 `update_residue_row`|`crates/aspis-r1-cost-probe/src/verifier.rs:235`|`61f3b29780d6123b0664dfa77c78d164e6821e0adbe958a196c50e2ea64d5595`|F192,F194|no|no cohort counterpart|Loop 237,243; B |residue|
|F196 `field`|`crates/aspis-r1-cost-probe/src/weights.rs:25`|`f144b4cb140af533df5bc6945181fa5e4bfd3bcd3e35ecf0ebf73b005d257263`|F048|no|M281|none|field|
|F197 `powers`|`crates/aspis-r1-cost-probe/src/weights.rs:7`|`46ab2d8c868cf1e62ebc76171fbd17d5f2dd37979997728d0928cf160298413d`|F007,F017,F029,F051|no|M062,M066|Loop 11; F mul|opening-transcript|
|F198 `decode_digest_canonical`|`crates/aspis-statement/src/atomic_statement.rs:91`|`9447e5ced470abb0a6360079409511e41ee3fb33de9a1a338cfbf616f36f5f6e`|F015|no|M241|none|public-hash|
|F199 `encode_digest_canonical`|`crates/aspis-statement/src/atomic_statement.rs:73`|`aa94a64ebf690ac127b49620ed33c40ca1dc38bb2164167861df3fd0bb19ca9d`|F022,F058|no|M242,M350|Loop 75; I; O digest.iter,digest.iter().enumerate|public-hash|
|F200 `unwrap_fixed_slice`|`crates/aspis-statement/src/atomic_statement.rs:84`|`7bc8124f1602fdb7c38d52d40297a6560186d4a41e17fc59137e9c523b59f3e4`||no|M243|none|public-hash|
|F201 `pool_v1_tree_parent`|`crates/aspis-statement/src/pool_v1/format.rs:241`|`6ee3e1e390571136aadfcdff0d78b6f8ffc2f8f2dd7b7008807ee59531fd734c`|F305|no|no cohort counterpart|none|public-hash|
|F202 `IncrementalMerkleTreeV1::default`|`crates/aspis-statement/src/pool_v1/incremental_merkle.rs:493`|`dc70c893e4f217ea26ca774dd4be02fd1365ccc5f6475d6359bd731aa5d6e7d7`|F203|no|no cohort counterpart|none|public-hash|
|F203 `IncrementalMerkleTreeV1::empty`|`crates/aspis-statement/src/pool_v1/incremental_merkle.rs:256`|`ebc9abfc802336a60c8f7659cfd601f133f81c50831c7ee278801871e6fdafae`|F204|no|no cohort counterpart|none|public-hash|
|F204 `pool_v1_empty_roots`|`crates/aspis-statement/src/pool_v1/incremental_merkle.rs:84`|`a6027f049a3c31b1c52f4302ba048cf8e279c7082785c592ee584fb4d9b47cb7`|F201|no|no cohort counterpart|Loop 86|public-hash|
|F205 `digest_is_canonical`|`crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs:166`|`152441898b4e704ebaaed3ae8286596dda09d6be4e65ae2653ab324f95e2c808`||no|M244|Loop 168; O digest.len|public-codec|
|F206 `first_canonical_byte`|`crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs:178`|`2dad3eb8cedd578208123ef5929a1a2cf82c686040a7ec2c45f2cbb0cf5621e0`|F199|no|M245|none|public-codec|
|F207 `pool_v1_pair_forest_output_lane_v1`|`crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs:184`|`8645de8546bf7663bb7b3933b8d0afc221bcedc2b43f9861eca0b8cee7dbee78`|F205,F206|no|M246|none|public-codec|
|F208 `Selectors::active`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:238`|`2c5f9843f8a3de74cdff673abc924e331697f072d831d6f7e7be8a36572fbdb2`|F209|no|M432|none|semantic-eval|
|F209 `Selectors::active_mask_basis`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:194`|`06327928dccdc523e4969b244f5b8d6d6a45a68e25da195713c9c9391d1d8c63`|F001,F007,F013,F017,F024,F029,F047,F051|no|no cohort counterpart|Loop 201,218; F add,mul|semantic-eval|
|F210 `Selectors::at_point`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:161`|`3cd0a59f4dd521f3582c30449cc53fc50d0bd774664b4f0036fb67623c8ed7cc`|F212|no|M433|none|semantic-eval|
|F211 `Selectors::boxed_at_point`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:169`|`a1b38fc77b6f9a7a5449de3829d55a83508335910770f69efa8a412638de00e7`|F210|no|M434|none|semantic-eval|
|F212 `Selectors::expand`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:144`|`72870aa156d7fff2902d5f79e54b851c8f69135737235109831fc1a6d6eddf3a`|F007,F012,F017,F021,F023,F029,F033,F051,F057|no|M435|Loop 148,150; I; F mul,sub|semantic-eval|
|F213 `Selectors::row`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:174`|`6e384de8987595f6977b7511a206049c687e77d8ef7df87dfabd1aaa33a0421b`|F007,F017,F029,F051|no|M436|F mul|semantic-eval|
|F214 `accumulate_endpoint_selector_tensor_basis`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:820`|`2d9421c7d79f9d8d9a8f7b5a86f111360e3db287f95b24c4879a639fc8ada5fd`|F001,F013,F024,F047,F226|no|no cohort counterpart|B ; F add|semantic-eval|
|F215 `copy_residual`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:353`|`d337c04540afccc38db5d7078647f6d7dd334a3dec628a5eb0998f82cc7903bc`|F001,F007,F012,F013,F017,F021,F024,F029,F033,F047,F051,F057|no|M437|F add,mul,sub|semantic-eval|
|F216 `copy_tag_coordinate_dot`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:692`|`7fb036830e7ba6316136b8803d17227ea10345a0995a20ba58e7d3284c03bbd3`|F001,F010,F013,F020,F024,F047|no|no cohort counterpart|Loop 696,699,709; F M31::reduce_u64,add|semantic-eval|
|F217 `copy_tag_coordinate_value`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:743`|`26a0429e391dee8094a40b1aabd6c5d1e982012ade1f18926520444d500b428b`|F216|no|no cohort counterpart|none|semantic-eval|
|F218 `evaluate_with_selectors`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:924`|`943bbe1d2c45a64f1bd851059b01547776fa7b5ef051b34efc266fa8e844b624`|F007,F017,F029,F051,F208,F214,F215,F220,F222,F223|no|M438|Loop 958; B 1046,1054; F mul|semantic-eval|
|F219 `finish_pattern_basis_values`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:791`|`13d49b06c2492291c427edf866f3385016bda99190116f78826d3340820d2ccb`|F001,F007,F013,F017,F024,F029,F047,F051|no|no cohort counterpart|Loop 797,799; F add,mul|semantic-eval|
|F220 `finish_selector_tensor_basis`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:850`|`504c25c7b38d3bd72d364eda75a74c2d9d5bccb70f04823ddc451fc922b8a3c3`|F001,F007,F013,F017,F024,F029,F047,F051,F217,F219,F225|no|no cohort counterpart|Loop 873,876,911; F add,mul|semantic-eval|
|F221 `lift_m31`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:114`|`18b986f571b272cca548735d36cd61bec0312abcc8acb3b842985905c6eaa74b`|F004,F025|no|M439|none|semantic-eval|
|F222 `link_weight`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:374`|`b86cfc49538533d30fcd66493fb9c726dc40252fbfd7c142a656170bb14ffe7a`||no|M440|none|semantic-eval|
|F223 `pattern_values`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:335`|`2638996d9eb8b1210efde6fa631b20f9a205e986c7c516d8dfed5086e49dab6f`|F224|no|M441|none|semantic-eval|
|F224 `pattern_values_windowed`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:283`|`e8b231003195740f4bf707f2d9bcfea889c1572c94350ab1f2219e88e1e82772`|F001,F007,F012,F013,F017,F021,F024,F029,F033,F047,F051,F057,F221|no|no cohort counterpart|Loop 290,299; I; F add,mul,sub|semantic-eval|
|F225 `qm31_sum_products_up_to4`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:722`|`c56b8bc9870aaa1d210da4f149eb6900e2aa4b4683feea5f35500657f076c883`|F007,F017,F029,F040,F041,F043,F051|no|no cohort counterpart|F mul|semantic-eval|
|F226 `selected_binary_weight`|`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs:811`|`dbd199ea5f74bf5de16671319cc5bc48577e3e5109213d5ea70c9203e4213881`||no|no cohort counterpart|none|semantic-eval|
|F227 `absorption_lanes_factored`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:351`|`f8a4b6d3077b8e3557f7c1f6ad09096cadafd23f4f6b4c9222d7bacbd2a4a88d`|F001,F007,F013,F017,F023,F024,F029,F047,F051|no|no cohort counterpart|F add,mul|semantic-eval|
|F228 `add_occupancy_lanes`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:544`|`d9500106e35c45325e9ee93fb7556861ed9726ba103945fd9849acb838835fb1`|F213,F230,F244,F265|no|M442|B |semantic-eval|
|F229 `add_path_lanes`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:408`|`2cb72727c5a5af29ad22f2bf3dbb2fbeca0766aa35a761cb835c5ce423f013c0`|F001,F007,F013,F017,F024,F029,F047,F051,F230,F247,F262|no|M443|B ; F add,mul|semantic-eval|
|F230 `add_preweighted`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:120`|`48cce7f31beafc8596cd6348c3f694ce398f727af6ab9b886c33fafab1015dfc`|F001,F013,F024,F039,F047|no|M444|Loop 127; B ; F add|semantic-eval|
|F231 `add_preweighted_shared_selector`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:149`|`4f4229a3d79646f34efc41d984a0218414e3a93557767f00160309ea2de08625`|F001,F007,F013,F017,F024,F029,F039,F047,F051|no|no cohort counterpart|Loop 157; B ; F add,mul|semantic-eval|
|F232 `add_schedule_lanes`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:396`|`9179b2d51ecca2cae6da861e781dba682bb1daa55608a8b16fec76d367923e7a`|F230,F260|no|M445|B |semantic-eval|
|F233 `add_value_lanes`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:480`|`e01906f45024c2ec2eb3c3664b550a19a03327332774e5c06ab5310bcd742a85`|F001,F007,F008,F011,F012,F013,F017,F021,F024,F029,F030,F032,F033,F047,F051,F052,F056,F057,F213,F230,F231,F257|no|M446|Loop 493,498,505; I; B ; F add,mul,mul_m31,square,sub|semantic-eval|
|F234 `append_level_packed_selector_tensor`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:901`|`fa565e254864875310cfab90e74a8d5ca7f50c9a559078c0e35eba38f22d9d24`|F001,F007,F012,F013,F017,F021,F023,F024,F029,F033,F039,F047,F051,F057,F239,F243|no|no cohort counterpart|F add,mul,sub|semantic-eval|
|F235 `append_levels_packed_selector_tensor`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:962`|`f028d64de4bba7c77181271e7370653155cbe295661967587ae6d3c299df5f1d`|F001,F013,F024,F047,F234|no|no cohort counterpart|Loop 974; F add|semantic-eval|
|F236 `bounded_append_carry`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:107`|`50faf72ae9b5bdfa6ccbb4c46f0986b1fa444bf2abcf2bfc2cc94af8a8dfb1b3`||no|M447|Loop 109|semantic-eval|
|F237 `composition_parts`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:1230`|`499f65133b57e879a1f3ed024c17945fb0d975887ad8e131bc0ce054bfb27bc0`|F001,F007,F013,F017,F023,F024,F029,F047,F051,F211,F218,F238,F248,F259,F261,F264,F308|no|M448|Loop 1284,1287; I; F add,mul|semantic-eval|
|F238 `copy_variant`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:1208`|`3b4bcf25c48c37afc8e5590444b5e662d29e4db49c9929b36bf4360012adcddf`||no|M449|none|semantic-eval|
|F239 `empty_root`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:190`|`327afb4d40b0c6e41ebd72112384dd0cb57d73ef44aa3d93acdfbe489e1a03b1`||no|M450|I|semantic-eval|
|F240 `equality_value`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:1215`|`e350ce6e539c5674cd87c6613897cb43ee57ab52f81d1c871f37e87f3fa4657f`|F007,F017,F024,F029,F033,F051|no|M451|Loop 1222; F add,mul,sub|semantic-eval|
|F241 `initial_variant_selectors`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:233`|`d9fe245a2bab751e86071986725fd06cf66f56a2bbefe655a0bf82e9af1e7a8b`|F001,F013,F024,F047|no|M452|F add|semantic-eval|
|F242 `left_digest_packed_selector_tensor`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:840`|`0040d5ca2e9068254b4591e7378b86ac109324ec0b6fd01eac20413e7aa00ff0`|F007,F012,F017,F021,F023,F029,F033,F039,F051,F057,F243|no|no cohort counterpart|F mul,sub|semantic-eval|
|F243 `lift_m31`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:101`|`18b986f571b272cca548735d36cd61bec0312abcc8acb3b842985905c6eaa74b`|F004,F025|no|M453|none|semantic-eval|
|F244 `occupancy_lanes_factored`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:595`|`ed6aab03e13549b9db0a8bfddeda5b78fa83371f640988ef231f07137cb9f363`|F001,F007,F012,F013,F017,F021,F023,F024,F029,F033,F047,F051,F057,F243|no|no cohort counterpart|Loop 612; F add,mul,sub|semantic-eval|
|F245 `optional_carry_packed_selector_tensor`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:996`|`f03d0e02cf983c980b2d8d19d420ed86afe44f973871eb596abfaae1b5478ab3`|F007,F012,F017,F021,F023,F029,F033,F039,F051,F057,F243|no|no cohort counterpart|F mul,sub|semantic-eval|
|F246 `optional_recipient_packed_selector_tensor`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:869`|`434787e888c9e5de13c6fa8db282243109d3b5f809ad5ca631ccf3204ce6b17a`|F007,F012,F017,F021,F023,F029,F033,F039,F051,F057,F243|no|no cohort counterpart|Loop 879; F mul,sub|semantic-eval|
|F247 `path_lanes_factored`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:444`|`82be995dbb46c9ead080de3ab45a513377c316c6aec5d30f9f25dff80d79872b`|F007,F012,F017,F021,F023,F029,F033,F051,F057|no|no cohort counterpart|F mul,sub|semantic-eval|
|F248 `poseidon_selectors`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:225`|`49c1d9497ced08def24323a067e97204d3e2fafb362e7f9f5ecc84532c7f635b`|F262|no|M454|none|semantic-eval|
|F249 `private_public`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:1327`|`4b244e5102190a9ddac0a34947f0d8fba477e400a90f6916a14d8d20d99e95af`||no|M133,M158,M455|none|semantic-eval|
|F250 `public_digest_packed`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:1124`|`fc44daa9ba77a01784a47faf64017e7a61bd0043ede2e00149451cb05ce08e4c`|F251|no|no cohort counterpart|none|semantic-eval|
|F251 `public_digest_packed_selector_tensor`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:1040`|`ef1afaa5cf67dbc47980119f3ff3b539d486059903b9fd7d24621a68d6191d17`|F001,F007,F013,F017,F023,F024,F029,F047,F051,F235,F236,F242,F245,F246|no|no cohort counterpart|F add,mul|semantic-eval|
|F252 `r0::Public<'a>::public_bytes::fields`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:2018`|`00f57adb431843f37869842a0157ff0088ce6d3c1656de10f3913736231bd1c1`|F022,F058|no|M135,M160|Loop 2019; B |semantic-eval|
|F253 `r0::Public<'a>::public_bytes::frontier`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:2029`|`393c489e5dae7525ee3f203bc729f11a6e1bbc16e54429f74b7022c61c27aff3`|F252|no|M136,M161|B |semantic-eval|
|F254 `r0::Public<'a>::public_bytes`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:2017`|`2045bbcd8a52a4a589fde36ff95e3aafcbae8244e569a634b3161d93c6d23e08`|F022,F058,F252,F253,F255|no|M134,M159|Loop 2019; B 2058,2059,2060,2063,2065,2068,2073,2074,2075|semantic-eval|
|F255 `r0::Public<'a>::semantic`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:2005`|`3b235f59c8e964228f3c63a8cefefe47d01684b19bba9be1235851b438edda6d`|F249,F266|no|M137,M162,M456|none|semantic-eval|
|F256 `r0::Public<'a>::terminal_qm31`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:2080`|`87514ce6f38e341534ce3aa0a80e08b577c914e6b912c315f8f1e1c57c6a67a6`|F255,F263|no|M457|I|semantic-eval|
|F257 `reconstruct_10`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:182`|`20ec4840700586b52da92c4e679115bb1427fcc969ee7c1db7a4f45d8723949a`|F001,F013,F024,F047|no|M458|I; F add|semantic-eval|
|F258 `scalar_lanes`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:1136`|`6ca80fe8eddf7cb823fc87475b1d96d8f35e02760dfedc53db662088b3ad4dbc`|F001,F013,F024,F047|no|M459|F add|semantic-eval|
|F259 `selected_claim`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:1199`|`a86dbad4d23bae456ca1e7abc382f6e5545007398af5ce4c413f9faeb587e498`||no|M460|none|semantic-eval|
|F260 `semantic_initial_and_absorption`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:255`|`2882d8e00e9546074b1effeb0210c77bdb0783bb623859d42a38986f60eb4d6d`|F001,F007,F008,F012,F013,F017,F021,F023,F024,F029,F030,F033,F047,F051,F052,F057,F227,F241,F262|no|M461|F add,mul,mul_m31,sub|semantic-eval|
|F261 `semantic_packed`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:1157`|`59b34976f029d802a74e13a69a1f7a066cd8fc5da77753d0bfa093a5fb2dc635`|F001,F007,F012,F013,F017,F021,F024,F029,F033,F047,F051,F057,F213,F228,F229,F230,F232,F233,F243,F250,F258|no|M462|B 1163,1164,1165,1166,1195; F add,mul,sub|semantic-eval|
|F262 `sum_high`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:171`|`b2e6928643d3e98e2463512f67c6cbbc94d018dbe093d878841b9bb80e81ba9c`|F001,F013,F024,F047|no|M463|Loop 173,174; F add|semantic-eval|
|F263 `terminal_parts`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:1300`|`9ca63ef7b7895b4f276329eadef663600f700fa26656a68a809c6e1d04059304`|F001,F007,F013,F017,F024,F029,F033,F047,F051,F237,F240|no|M464|F add,mul,sub|semantic-eval|
|F264 `validate_transition`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:194`|`956fa7c38be0d7299ebf359622078e85e25e0cb1cc0973930173e07105fca012`|F236,F239|no|M465|Loop 209|semantic-eval|
|F265 `variant_expected_output`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:536`|`81ddc59f1a0ec502c11ea515cf548de644851bc3f7bf30a1fd5ea47193a46acf`||no|M466|none|semantic-eval|
|F266 `withdrawal_public`|`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:1345`|`0d66be9cf3b8cf5dbb344cbba8fcd365e2d9737625acc1d061c34c462ccba559`||no|M138,M163,M467|none|semantic-eval|
|F267 `PoolV1PairForestTerminalStatementV1::common`|`crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:133`|`6d1d7420e53e28e2550bd15b2af42d52b77763e2afcc4b12b5a07cf8653ed818`||no|M247|none|public-codec|
|F268 `PoolV1PairForestTerminalStatementV1::semantic_public`|`crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:120`|`cefd39cf61e4755559619d43ff4951205b5a61b1dd5870f0234838ad855fbbab`||no|no cohort counterpart|none|public-codec|
|F269 `decode_lane_transition_boxed_v1`|`crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:332`|`2458f6b50566ab5506b0a910ba01049fef787d0a3fb0b87524500674ca17b466`|F283|no|M248|none|public-codec|
|F270 `decode_pool_v1_pair_forest_terminal_statement_v1`|`crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:400`|`8ab070c15b19caac434f13d2efdf3c4a72e992c1f6cac24c20e983eef165c81c`|F271,F272,F273,F275,F276|no|M249|none|public-codec|
|F271 `decode_terminal_common_boxed_v1`|`crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:340`|`09948d5d6c74b4fd0c788159e83f5cdaff0790ea0d06777ad0ed447a246f67d0`|F198,F269|no|M250|none|public-codec|
|F272 `decode_transfer_statement_boxed_v1`|`crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:373`|`fbaeee71614628f7cd3a47950ee38241cbed328f316b67dd948a28ac42cdbc5b`|F290|no|M251|none|public-codec|
|F273 `decode_withdrawal_statement_boxed_v1`|`crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:388`|`8328071ec8cbfbac989967a02949a108e3373e8582ea65119ca364301b193b89`|F291|no|M252|none|public-codec|
|F274 `statement_public_common`|`crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:218`|`af1f5bef075c884a080199927a8370a4eba5f99bef43d7a0088dff08e2cc257c`||no|M253|none|public-codec|
|F275 `transition_kind`|`crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:204`|`64491100c34a489a2127da66f112551f9977769631a9a932aa27d148e511ab73`||no|M254|none|public-codec|
|F276 `validate_pool_v1_pair_forest_terminal_statement_v1`|`crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:241`|`54650bd1a71a536a37706da4d10af1e02a05548f99b2439acd94b515991b67f6`|F207,F267,F274,F286,F294,F295|no|M255|B 287|public-codec|
|F277 `decode_pool_v1_pair_verified_afterstate_v1`|`crates/aspis-statement/src/pool_v1/pair_terminal.rs:161`|`927ff4b460f1542d8775a4646e88718fe5d9829960ef943d24070857d2d693c0`|F198,F279,F280|no|M256|none|public-codec|
|F278 `encode_pool_v1_pair_verified_afterstate_v1`|`crates/aspis-statement/src/pool_v1/pair_terminal.rs:142`|`49b5f1b02e09883dc72f30781d2178622c6dcfb19146435765e6d2d6a480fecc`|F022,F058,F199,F280|no|M257|Loop 154; I|public-codec|
|F279 `exact`|`crates/aspis-statement/src/pool_v1/pair_terminal.rs:235`|`c754289743de065e205cbffec48df5613e151f18b2a1084b0e13c0a00dc097e9`||no|M258|none|public-codec|
|F280 `validate_verified_afterstate`|`crates/aspis-statement/src/pool_v1/pair_terminal.rs:122`|`3fde513e91c9b47bfce780d430d01a496f5f067df920944a1580ba6cf4a04953`|F285|no|M259|Loop 133|public-codec|
|F281 `decode_pair_afterstate_boxed_v1`|`crates/aspis-statement/src/pool_v1/pair_tree_profile.rs:672`|`0ef043d6153d90a6fb109fa34f3d9b8d1a9f02d6091c134cf3650ea9ee6ce529`|F277|no|M260|none|public-codec|
|F282 `decode_pair_live_snapshot_boxed_v1`|`crates/aspis-statement/src/pool_v1/pair_tree_profile.rs:662`|`9772e7c69bd301fe6f471c91cdd79cb818fa61ce6a0c68697cab7c83bfb9d256`|F284|no|M261|none|public-codec|
|F283 `decode_pool_v1_pair_late_public_statement_boxed_v1`|`crates/aspis-statement/src/pool_v1/pair_tree_profile.rs:681`|`b5100dfbe9fe422415cb913ea4d89f193536b338d4cab2c0a606c2cd39cb8942`|F200,F281,F282|no|M262|none|public-codec|
|F284 `decode_pool_v1_pair_live_snapshot_v1`|`crates/aspis-statement/src/pool_v1/pair_tree_profile.rs:500`|`f64d35491c32a2e0118af8b7745bd033dcb5645ba1fc2d35787f0a2510291dad`|F198,F200,F288|no|M263|none|public-codec|
|F285 `digest_is_canonical`|`crates/aspis-statement/src/pool_v1/pair_tree_profile.rs:105`|`7d5a3f0d380322fec9e60dd8ea6cf0456ce7a10a3290abcf0d2d38d6325c0153`||no|M264|Loop 107|public-codec|
|F286 `encode_pool_v1_pair_late_public_statement_v1`|`crates/aspis-statement/src/pool_v1/pair_tree_profile.rs:627`|`3a9b09f4d994c441f740296c37e42fb4047fa3a3d9e67d9e141a2ea775ed0c05`|F022,F058,F278,F287|no|M265|B 651|public-codec|
|F287 `encode_pool_v1_pair_live_snapshot_v1`|`crates/aspis-statement/src/pool_v1/pair_tree_profile.rs:475`|`40a3fda06a90ef030949ae87e3986846bda6e49babc9553679dcba17e4696ae9`|F022,F058,F199,F288|no|M266|Loop 493; I; B |public-codec|
|F288 `validate_pool_v1_pair_live_snapshot_v1`|`crates/aspis-statement/src/pool_v1/pair_tree_profile.rs:450`|`3d4884efe78c0667b11c84e7ec9ec599df234d56ca624c320af0b43c08297bba`|F285|no|M267|Loop 466|public-codec|
|F289 `decode_common`|`crates/aspis-statement/src/pool_v1/payment_relation.rs:344`|`cb1197d7e85e3a73dd7ea9d3c8015b5d8c5f51e237958c07a6c39966259121ae`|F198,F200,F298|no|M268|none|public-codec|
|F290 `decode_pool_v1_private_transfer_public_v1`|`crates/aspis-statement/src/pool_v1/payment_relation.rs:377`|`d8c493d1aca1abf9195e9d910250ae1320a52c063f61cc38de8ddf409f329061`|F022,F058,F198,F200,F289,F296,F299|no|M269|none|public-codec|
|F291 `decode_pool_v1_withdrawal_public_v1`|`crates/aspis-statement/src/pool_v1/payment_relation.rs:414`|`bfa31717b99e732ca363e96bf57d7ddcbd58d2c023dd8f166e33742777e428cf`|F198,F200,F289,F296,F300|no|M270|none|public-codec|
|F292 `digest_is_canonical`|`crates/aspis-statement/src/pool_v1/payment_relation.rs:178`|`b3552691911298d69adbf28b8ddbc5403ba52ee1a9b6c70c9654f9120b84d505`||no|M271,M287,M293|none|public-codec|
|F293 `encode_common`|`crates/aspis-statement/src/pool_v1/payment_relation.rs:255`|`b5615d3c2856a9668062e4fdd8764645200096ff3f2b1eec0ecc85115d73fb42`|F022,F058,F199|no|M272,M288|B |public-codec|
|F294 `encode_pool_v1_private_transfer_public_v1`|`crates/aspis-statement/src/pool_v1/payment_relation.rs:278`|`f3f06ec2303f65f6448bf702f4af59c2d039344aaa7b17a237cf207002ecd256`|F199,F293,F297,F299|no|M273|B 284|public-codec|
|F295 `encode_pool_v1_withdrawal_public_v1`|`crates/aspis-statement/src/pool_v1/payment_relation.rs:301`|`7b5224ac0b2f602f976f787bce5c69930af6f2726a29c9e4790dbb5efd982de7`|F022,F058,F199,F293,F300,F301|no|M274,M289|B 307|public-codec|
|F296 `require_header`|`crates/aspis-statement/src/pool_v1/payment_relation.rs:321`|`42ca936d08b50d27aaa73a205c09fbbed12cbc602c287f0c3f33f4c2f8e8cd49`||no|M275|none|public-codec|
|F297 `transfer_common`|`crates/aspis-statement/src/pool_v1/payment_relation.rs:205`|`045ace39e5cba5d43b19f21bd7b4837fd220a321b82f4beef9dd13e8172f90a3`||no|M276|none|public-codec|
|F298 `validate_common`|`crates/aspis-statement/src/pool_v1/payment_relation.rs:189`|`ba4de7c65a57550bec922bbb44be8f3b75a0c5e020e229a782fae1877c241724`|F292|no|M277,M290,M294|none|public-codec|
|F299 `validate_pool_v1_private_transfer_public_v1`|`crates/aspis-statement/src/pool_v1/payment_relation.rs:227`|`35cfd05f4a771e62afea011ce3cb43e6d3d696c54cc49f7b8b9b38186ddf02a2`|F292,F297,F298|no|M278|none|public-codec|
|F300 `validate_pool_v1_withdrawal_public_v1`|`crates/aspis-statement/src/pool_v1/payment_relation.rs:239`|`4bfa77f64e9c57757580ad44723ba309adbc3b2e3105ee2d5d632a0ade4b85e9`|F292,F298,F301|no|M279,M291,M295|none|public-codec|
|F301 `withdrawal_common`|`crates/aspis-statement/src/pool_v1/payment_relation.rs:216`|`045ace39e5cba5d43b19f21bd7b4837fd220a321b82f4beef9dd13e8172f90a3`||no|M280,M292,M296|none|public-codec|
|F302 `apply_mat4_lazy`|`crates/aspis-statement/src/poseidon2.rs:176`|`593f9015765e3d52eb07a324b690118f3a5c7755c4d82908bf44e7d0fa9ebd22`|F019|no|no cohort counterpart|B |public-hash|
|F303 `external_linear_lazy`|`crates/aspis-statement/src/poseidon2.rs:188`|`b5712d6cf182a1fbee7c6767db0b74a5ae1616bcb32aaf5ad4ee23cf09000e4f`|F019,F302|no|no cohort counterpart|Loop 189,194; I; B |public-hash|
|F304 `internal_linear_lazy`|`crates/aspis-statement/src/poseidon2.rs:224`|`9a32cc3ce561c7abcf77fb1884e7a5e6ac64c73087eb6be2be06caef21c6d6a5`|F019|no|no cohort counterpart|Loop 228; I; B |public-hash|
|F305 `merkle_node_compress_v3`|`crates/aspis-statement/src/poseidon2.rs:495`|`476491f4cb87936f2538797bc45399703339d999858615dcae906fd9074a059b`|F001,F013,F024,F047,F306|no|no cohort counterpart|B 502; F add|public-hash|
|F306 `permute_optimized_with_trace`|`crates/aspis-statement/src/poseidon2.rs:362`|`bb51cc19d0611b8808c6ae0a7cb8100ce74a9f532ade5878177b602c9a16ab91`|F001,F013,F024,F047,F303,F304,F307|no|no cohort counterpart|Loop 369,370,383,395,396; I; B ; F add|public-hash|
|F307 `pow5`|`crates/aspis-statement/src/poseidon2.rs:137`|`2aa900ce6bde046971ed173f7a26cadcfadb9d86de5711854efb9c2c93f064e3`|F007,F017,F029,F051|no|no cohort counterpart|F mul|public-hash|
|F308 `evaluate_state_only_poseidon_oracle_projected`|`crates/aspis-statement/src/state_only_poseidon.rs:585`|`e37bfe40faf1e9e90d0b149ee3cdc2cb954a430911eabeb9eb9a0a516c6a4677`|F001,F007,F012,F013,F017,F021,F023,F024,F029,F033,F039,F042,F047,F051,F057,F323,F324,F325|no|M468|I; F add,mul,sub; O prepared_block.mul|public-hash|
|F309 `extension_from_raw_limbs`|`crates/aspis-statement/src/state_only_poseidon.rs:135`|`ffacebbd08c41397d8159879a5c81cf20c5fef66611a843083f53a7937c4197e`|F010,F019|no|M220,M469|none|public-hash|
|F310 `extension_limbs`|`crates/aspis-statement/src/state_only_poseidon.rs:130`|`567433549f10a4306927d541ffd872f6797800a6403f8fb8c0424e4a37ce9983`||no|M470|none|public-hash|
|F311 `external_linear_lazy`|`crates/aspis-statement/src/state_only_poseidon.rs:144`|`72e129de72a0624a389a56352a48dadef14dd1a3bac387bbddef3d891104b2cc`|F309,F310|no|M471|Loop 146,156,184; I; B |public-hash|
|F312 `external_linear_packed`|`crates/aspis-statement/src/state_only_poseidon.rs:281`|`2e4b8bd3f2484561fa6b1231da9d241d254e37889c0556ea20bc0401d9357903`|F001,F013,F024,F047,F313|no|M472|Loop 284; I; F add|public-hash|
|F313 `external_local_packed`|`crates/aspis-statement/src/state_only_poseidon.rs:265`|`32315b5776a62a1a2416f25638ea24dc516474ceddbb4c062fa1680dd9b8b077`|F309,F314|no|M473|none|public-hash|
|F314 `external_local_packed_raw`|`crates/aspis-statement/src/state_only_poseidon.rs:217`|`81cdec4685fead3a7460023f1a614563a84ccfcf72e21b8ad393bd448a11b460`||no|M474|Loop 236,238; I|public-hash|
|F315 `full_round`|`crates/aspis-statement/src/state_only_poseidon.rs:332`|`3865f73234e0e7d1ef4aba9ad35ffcceb7c4c3ac75205fd564c221548d3bc60c`|F001,F013,F024,F047,F311,F326|no|M475|Loop 336; B 339; F add|public-hash|
|F316 `full_round_m31_constants`|`crates/aspis-statement/src/state_only_poseidon.rs:347`|`d830b0c37ddb3a57d0727339a737f878e44d5bbc82ce1047effba4c77f7f2874`|F001,F013,F024,F047,F311,F326|no|M476|Loop 351; B 355; F add|public-hash|
|F317 `full_round_m31_constants_packed`|`crates/aspis-statement/src/state_only_poseidon.rs:371`|`2ea47e1fabd27a667c17c93373a0fcae700eff1a4f047637d1a79d114f0c6d28`|F001,F013,F024,F047,F312,F326|no|M477|Loop 375; F add|public-hash|
|F318 `full_round_packed`|`crates/aspis-statement/src/state_only_poseidon.rs:360`|`9ed825b868436c42a05d2c14db486e5c56e9ff6862397180ef297e4d330740fc`|F001,F013,F024,F047,F312,F326|no|M478|Loop 364; F add|public-hash|
|F319 `internal_linear_lazy`|`crates/aspis-statement/src/state_only_poseidon.rs:304`|`43ad7bb1bd36a55d3b8c0e7f269e4f9d420e84a2b2840a7f7106e45bf5b330c2`|F309,F310|no|M479|Loop 309,312,323; B |public-hash|
|F320 `internal_round`|`crates/aspis-statement/src/state_only_poseidon.rs:383`|`05eb8981a7da57ff8c603032d76f8c3e9137129eaf8fc7e237870959d056b543`|F001,F013,F024,F047,F319,F326|no|M480|B 385; F add|public-hash|
|F321 `interpolate_three_constant_columns`|`crates/aspis-statement/src/state_only_poseidon.rs:432`|`9f4ec623bbce733081e96300b413c0791d1bf7668efe6b36967e2962aa0dfc5a`|F010,F322|no|M481|Loop 440|public-hash|
|F322 `interpolate_three_constant_limb`|`crates/aspis-statement/src/state_only_poseidon.rs:416`|`1342ef5458aaabd5a8b00d1b739dc8155256ef45c9d543c4c1d793f2b4840fa1`|F020|no|M482|F M31::reduce_u64|public-hash|
|F323 `interpolated_full_pair_packed`|`crates/aspis-statement/src/state_only_poseidon.rs:504`|`3b584cae6449d87f9d5391f7c4a8d7f0e4454365b09a7da8a5b6cc1d31562499`|F315,F318,F321|no|M483|none|public-hash|
|F324 `interpolated_internal_pair`|`crates/aspis-statement/src/state_only_poseidon.rs:524`|`6e98844a91597ed544a8650ca88c9ef59dc668d47ee7b8ae6ed0a2022e50b4aa`|F038,F320|no|M484|I|public-hash|
|F325 `leading_pair_packed`|`crates/aspis-statement/src/state_only_poseidon.rs:401`|`f89b17f4e8a310d3d127e376da5427f3d89e62adf6f88179662216f18cd11db5`|F001,F013,F024,F047,F311,F316,F317|no|M485|Loop 405; B 408; F add|public-hash|
|F326 `pow5`|`crates/aspis-statement/src/state_only_poseidon.rs:124`|`b316329b611c940d8325cc4d842763ee07fbe8f97a76d775995d0139c3530086`|F007,F011,F017,F029,F032,F051,F056|no|M486|F mul,square|public-hash|
|F327 `SolanaDigest::digest`|`programs/r1-cost-probe/src/lib.rs:13`|`bf350001bb35be594630c2acf4777532da5e2b23ef3d2837fd5ad7b185720979`||no|M047|O hashv,hashv(parts).to_bytes|oracle|
|F328 `first_decoded`|`programs/r1-cost-probe/src/lib.rs:49`|`0217165d1d3e232a16e43111e6e84053de77d764ec4dad9e0d874403a6443da2`|F094,F329|no|M002,M048|none|wrapper|
|F329 `observer`|`programs/r1-cost-probe/src/lib.rs:36`|`9b5e474385ebe3d7c497f0e5b3130e0fea59352f945511dd96de5817b9200fe9`||no|M003|none|control|
|F330 `process_r1_cost_probe_instruction`|`programs/r1-cost-probe/src/lib.rs:56`|`a898600975893510c1826c0aba19d8c970548126f20a1491d26568c314e33292`|F331,F333|no|M018|none|entry|
|F331 `admitted`|`programs/r1-cost-probe/src/pool_route.rs:3`|`07f037b6a6f10634575dbed6af67c5ef9bd20930dd2e730992f3b70b6742a9ad`||no|no cohort counterpart|none|entry|
|F332 `decode_public_statement_box`|`programs/r1-cost-probe/src/r1_pool_adapter.rs:237`|`2d41c2d955de49ddf48fecd9d327bec267d1f6c3f1bafb5f4214ef1f38108203`|F270|no|no cohort counterpart|none|wrapper|
|F333 `process`|`programs/r1-cost-probe/src/r1_pool_adapter.rs:950`|`326a0777fafcbe2c3158c58701410c201378e5dfbf4b0340c0614b1086ac87f4`|F344|no|no cohort counterpart|none|wrapper|
|F334 `readonly_buffer_meta_ok`|`programs/r1-cost-probe/src/r1_pool_adapter.rs:191`|`f525f87200df0e77904d7d481ad9851bb7eb298b211f8ae529be4125301ad140`||no|M013|none|wrapper|
|F335 `OwnedAccount::data`|`programs/r1-cost-probe/src/r1_pool_adapter_owned.rs:21`|`fb4f3f8629f4264a6e0327e7234b67673e880d7312a28db2d4f4c6ab0c566582`||no|M004|none|wrapper|
|F336 `OwnedAccount::data_len`|`programs/r1-cost-probe/src/r1_pool_adapter_owned.rs:24`|`b6b47c6b0dbcc158295b75660e0d192a7663893f39e36b3434d6ab103e4fb1c6`||no|M005|none|wrapper|
|F337 `OwnedAccount::key`|`programs/r1-cost-probe/src/r1_pool_adapter_owned.rs:19`|`f454b5292d6442a3f48ddd2a16e7175b38fb920896d6ebbb67d84542540353cf`||no|M006|none|wrapper|
|F338 `OwnedAccount::owner`|`programs/r1-cost-probe/src/r1_pool_adapter_owned.rs:20`|`36e0acc8a123d64ed3ddeadab513aec1e3ac407bb26d8984a7b6d4aeb5dbd0eb`||no|M007|none|wrapper|
|F339 `require_distinct_accounts`|`programs/r1-cost-probe/src/r1_pool_adapter_owned.rs:59`|`b07389e164bb28fa24ba425b7ba96a5f40d6397b4f947568405b46d987e37539`|F337|no|M008|Loop 61,63|wrapper|
|F340 `require_readonly_buffer`|`programs/r1-cost-probe/src/r1_pool_adapter_owned.rs:45`|`e6526943c6084ecbfc0ba52c72e0b9457c2664128126660e2fcb99780000320e`|F334|no|M009|none|wrapper|
|F341 `require_verifier_checkpoint`|`programs/r1-cost-probe/src/r1_pool_adapter_owned.rs:51`|`cae0701733b9cccf030b69bd3bd9de0dc96acc95cd01505caefc57cc12ae7174`|F187,F336,F338|no|M010|none|wrapper|
|F342 `require_zero`|`programs/r1-cost-probe/src/r1_pool_adapter_owned.rs:73`|`5cb1d59ffda0353ac5eee08763b841f8c03961eea240dacc29fdc55195e6ff2b`||no|M011|Loop 74|wrapper|
|F343 `snapshot`|`programs/r1-cost-probe/src/r1_pool_adapter_owned.rs:29`|`3565c41d56bc16abaaf18d148284c93663137e78b3b90093dfe7a860dd753367`||no|no cohort counterpart|none|wrapper|
|F344 `stage1`|`programs/r1-cost-probe/src/r1_pool_adapter_owned.rs:447`|`34414a1a05b8beca445d8e93a5e481aa0169a1b9ab545c154f9ce379487d8f53`|F343,F345|no|M046|none|wrapper|
|F345 `stage1_owned`|`programs/r1-cost-probe/src/r1_pool_adapter_owned.rs:376`|`9c0e47167f698df1849ed9c80e6f8201c397033610630bad6ad23ef1a55d4310`|F173,F267,F268,F276,F278,F328,F332,F335,F339,F340,F341,F342|no|M012,M049|none|wrapper|

## Exact cohort declaration index

Module ownership is the retained replay audit's recorded owner; local source filenames may be import-only copies. Every name here occurs in RPx's actual dependency closure. Full source hashes, inherited audit references and replay-tops3 membership are in JSON. These are model definitions, not newly asserted Rust equalities.

| Model | Lean name | Replayed module | Located source |
|---|---|---|---|
|M001|`AdapterRw.aspis_r1_cost_probe.transport.Variant.tag`|`AdapterRwModel`|`docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean:465`|
|M002|`AdapterRw.first_decoded`|`AdapterRwModel`|`docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean:654`|
|M003|`AdapterRw.observer`|`AdapterRwModel`|`docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean:648`|
|M004|`AdapterRw.r1_pool_adapter.owned.OwnedAccount.data`|`AdapterRwModel`|`docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean:845`|
|M005|`AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len`|`AdapterRwModel`|`docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean:860`|
|M006|`AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.key`|`AdapterRwModel`|`docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean:829`|
|M007|`AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.owner`|`AdapterRwModel`|`docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean:837`|
|M008|`AdapterRw.r1_pool_adapter.owned.require_distinct_accounts`|`AdapterRwModel`|`docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean:1010`|
|M009|`AdapterRw.r1_pool_adapter.owned.require_readonly_buffer`|`AdapterRwModel`|`docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean:869`|
|M010|`AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint`|`AdapterRwModel`|`docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean:889`|
|M011|`AdapterRw.r1_pool_adapter.owned.require_zero`|`AdapterRwModel`|`docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean:1054`|
|M012|`AdapterRw.r1_pool_adapter.owned.stage1_owned`|`AdapterRwModel`|`docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean:2857`|
|M013|`AdapterRw.r1_pool_adapter.readonly_buffer_meta_ok`|`AdapterRwModel`|`docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean:807`|
|M014|`AspisC2HostEmbedding.field.wide_exact.WideExact.from_qm31`|`AspisC2HostEmbedding.Funs`|`docs/research/100bit-spend-path-20261013/lean/c2-host-embedding-20261017/AspisC2HostEmbedding/Funs.lean:68`|
|M015|`AspisC2HostEmbedding.field.wide_exact.canonical_qm31`|`AspisC2HostEmbedding.Funs`|`docs/research/100bit-spend-path-20261013/lean/c2-host-embedding-20261017/AspisC2HostEmbedding/Funs.lean:42`|
|M016|`AspisR1.CheckpointBytes5Writer.writer`|`CheckpointBytes5Writer`|`docs/research/100bit-spend-path-20261013/lean/CheckpointBytes5Writer.lean:42`|
|M017|`AspisR1.CheckpointBytesBody.fields`|`CheckpointBytesBody`|`docs/research/100bit-spend-path-20261013/lean/CheckpointBytesBody.lean:19`|
|M018|`AspisR1.DrvC_SourceEntry.source`|`RPz7_DrvC_SourceEntry`|`evidence/replay-dry8-20261026/RPz7_DrvC_SourceEntry.lean:14`|
|M019|`AspisR1.FIp_DotDecode.field.CM31.from_le_bytes`|`RPz7_FIp_DotDecode`|`evidence/replay-dry8-20261026/RPz7_FIp_DotDecode.lean:65`|
|M020|`AspisR1.FIp_DotDecode.field.M31.from_le_bytes`|`RPz7_FIp_DotDecode`|`evidence/replay-dry8-20261026/RPz7_FIp_DotDecode.lean:55`|
|M021|`AspisR1.FIp_DotDecode.field.QM31.from_le_bytes`|`RPz7_FIp_DotDecode`|`evidence/replay-dry8-20261026/RPz7_FIp_DotDecode.lean:103`|
|M022|`AspisR1.FIp_NativeDots.fast_dots.four_dots`|`RPz7_FIp_NativeDots`|`evidence/replay-dry8-20261026/RPz7_FIp_NativeDots.lean:287`|
|M023|`AspisR1.FIp_NativeDots.fast_dots.four_dots_one`|`RPz7_FIp_NativeDots`|`evidence/replay-dry8-20261026/RPz7_FIp_NativeDots.lean:207`|
|M024|`AspisR1.Port3_BatchStd.sameIndex`|`Port3_BatchStd`|`docs/research/100bit-spend-path-20261013/lean/Port3_BatchStd.lean:38`|
|M025|`AspisR1.Port3_BatchStd.sameLeaf`|`Port3_BatchStd`|`docs/research/100bit-spend-path-20261013/lean/Port3_BatchStd.lean:33`|
|M026|`AspisR1.Port3_FlushInstall.flush`|`Port3_FlushInstall`|`docs/research/100bit-spend-path-20261013/lean/Port3_FlushInstall.lean:20`|
|M027|`AspisR1.Port3_Initial.constructor`|`Port3_Initial`|`docs/research/100bit-spend-path-20261013/lean/Port3_Initial.lean:39`|
|M028|`AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_merkle`|`Port3_NativeBatchBody`|`docs/research/100bit-spend-path-20261013/lean/Port3_NativeBatchBody.lean:277`|
|M029|`AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_merkle_values`|`Port3_NativeBatchBody`|`docs/research/100bit-spend-path-20261013/lean/Port3_NativeBatchBody.lean:233`|
|M030|`AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_tree`|`Port3_NativeBatchBody`|`docs/research/100bit-spend-path-20261013/lean/Port3_NativeBatchBody.lean:202`|
|M031|`AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range`|`Port3_NativeGeometryBody`|`docs/research/100bit-spend-path-20261013/lean/Port3_NativeGeometryBody.lean:432`|
|M032|`AspisR1.Port3_NativePendingInstall.source`|`Port3_NativePendingInstall`|`docs/research/100bit-spend-path-20261013/lean/Port3_NativePendingInstall.lean:26`|
|M033|`AspisR1.Port3_NativeQueryBody.verifier.accumulate_batched_with_node`|`Port3_NativeQueryBody`|`docs/research/100bit-spend-path-20261013/lean/Port3_NativeQueryBody.lean:162`|
|M034|`AspisR1.Port3_NativeQueryBody.verifier.candidate.query_loop`|`Port3_NativeQueryBody`|`docs/research/100bit-spend-path-20261013/lean/Port3_NativeQueryBody.lean:344`|
|M035|`AspisR1.Port3_NativeQueryBody.verifier.candidate.query_values`|`Port3_NativeQueryBody`|`docs/research/100bit-spend-path-20261013/lean/Port3_NativeQueryBody.lean:236`|
|M036|`AspisR1.Port3_NativeRowFrame.push`|`Port3_NativeRowFrame`|`docs/research/100bit-spend-path-20261013/lean/Port3_NativeRowFrame.lean:10`|
|M037|`AspisR1.Port4B_CountInstall.nodeCount`|`Port4B_CountInstall`|`docs/research/100bit-spend-path-20261013/lean/Port4B_CountInstall.lean:17`|
|M038|`AspisR1.Port4B_KeyInstall.keyArray`|`Port4B_KeyInstall`|`docs/research/100bit-spend-path-20261013/lean/Port4B_KeyInstall.lean:19`|
|M039|`AspisR1.Port4B_LeafCode.codeFor`|`Port4B_LeafCode`|`docs/research/100bit-spend-path-20261013/lean/Port4B_LeafCode.lean:22`|
|M040|`AspisR1.Port4B_Opening.opening`|`Port4B_Opening`|`docs/research/100bit-spend-path-20261013/lean/Port4B_Opening.lean:13`|
|M041|`AspisR1.Port4B_SlotInstall.nodeSlot`|`Port4B_SlotInstall`|`docs/research/100bit-spend-path-20261013/lean/Port4B_SlotInstall.lean:24`|
|M042|`AspisR1.Port4B_SlotInstall.offset`|`Port4B_SlotInstall`|`docs/research/100bit-spend-path-20261013/lean/Port4B_SlotInstall.lean:14`|
|M043|`AspisR1.Port4B_SortInstall.key_stream`|`Port4B_SortInstall`|`docs/research/100bit-spend-path-20261013/lean/Port4B_SortInstall.lean:15`|
|M044|`AspisR1.Port4B_VerifyInstall.verify`|`Port4B_VerifyInstall`|`docs/research/100bit-spend-path-20261013/lean/Port4B_VerifyInstall.lean:15`|
|M045|`AspisR1.Port4C_NativePrefix.verifier.batch_prefix_products`|`Port4C_NativePrefix`|`docs/research/100bit-spend-path-20261013/lean/Port4C_NativePrefix.lean:47`|
|M046|`AspisR1.S2W_D189Wrappers.first`|`S2W_D189Wrappers`|`docs/research/100bit-spend-path-20261013/lean/S2W_D189Wrappers.lean:63`|
|M047|`AspisR1.S2W_DigestExtraction.digest`|`S2W_DigestExtraction`|`docs/research/100bit-spend-path-20261013/lean/S2W_DigestExtraction.lean:23`|
|M048|`AspisR1.S2W_Outer.first_decoded`|`S2W_Outer`|`docs/research/100bit-spend-path-20261013/lean/S2W_Outer.lean:184`|
|M049|`AspisR1.S2W_Outer.stage1_owned`|`S2W_Outer`|`docs/research/100bit-spend-path-20261013/lean/S2W_Outer.lean:198`|
|M050|`AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64`|`AspisR1BatchedWeightsExtraction.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-source-proof-loops-20261019/AspisR1BatchedWeightsExtraction/Funs.lean:42`|
|M051|`AspisR1BatchedWeightsExtraction.aspis_core.field.reduce_u64`|`AspisR1BatchedWeightsExtraction.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-source-proof-loops-20261019/AspisR1BatchedWeightsExtraction/Funs.lean:25`|
|M052|`AspisR1BatchedWeightsExtraction.batched_weights.BatchedWeights.value`|`AspisR1BatchedWeightsExtraction.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-source-proof-loops-20261019/AspisR1BatchedWeightsExtraction/Funs.lean:137`|
|M053|`AspisR1CandidateParser.field.CM31.from_le_bytes`|`R1CandidateFieldParsers`|`docs/research/100bit-spend-path-20261013/lean/CandidateFieldParsers.lean:91`|
|M054|`AspisR1CandidateParser.field.M31.from_le_bytes`|`R1CandidateFieldParsers`|`docs/research/100bit-spend-path-20261013/lean/CandidateFieldParsers.lean:81`|
|M055|`AspisR1CandidateParser.field.QM31.from_le_bytes`|`R1CandidateFieldParsers`|`docs/research/100bit-spend-path-20261013/lean/CandidateFieldParsers.lean:129`|
|M056|`AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes`|`R1CandidateWideParserSource`|`docs/research/100bit-spend-path-20261013/lean/CandidateWideParserSource.lean:29`|
|M057|`AspisR1CanonicalDotFinish.canonical.Dot.finish`|`AspisR1CanonicalDotFinish.Funs`|`docs/research/100bit-spend-path-20261013/lean-candidates/canonical-dot-finish-source-20261020/sources/AspisR1CanonicalDotFinish/Funs.lean:54`|
|M058|`AspisR1CanonicalDotFinish.canonical.reduce`|`AspisR1CanonicalDotFinish.Funs`|`docs/research/100bit-spend-path-20261013/lean-candidates/canonical-dot-finish-source-20261020/sources/AspisR1CanonicalDotFinish/Funs.lean:27`|
|M059|`AspisR1CircleSampleWrapper.sampler.circle_sample`|`AspisR1CircleSampleWrapper.Funs`|`evidence/leaf-p6-14-20261027/LPp_WrapperFuns.lean:49`|
|M060|`AspisR1ClaimsUnrolledParent.aspis_core.r0.heap.filled`|`ClaimsUnrolledParentSource`|`docs/research/100bit-spend-path-20261013/lean/ClaimsUnrolledParentSource.lean:111`|
|M061|`AspisR1ClaimsUnrolledParent.candidate_claims.claims`|`ClaimsUnrolledParentSource`|`docs/research/100bit-spend-path-20261013/lean/ClaimsUnrolledParentSource.lean:173`|
|M062|`AspisR1CurrentCaller.OriginalPreparedSource.powers`|`CurrentOriginalPreparedCarrierTransportV1`|`evidence/port17release-20261024/dependency-source/CurrentOriginalPreparedCarrierTransportV1.lean:56`|
|M063|`AspisR1CurrentCaller.verifier.candidate.prepare`|`CurrentCompactCallerModelV1`|`evidence/port17release-20261024/dependency-source/CurrentCompactCallerModelV1.lean:194`|
|M064|`AspisR1CurrentCaller.verifier.candidate.tx1`|`CurrentCompactCallerModelV1`|`evidence/port17release-20261024/dependency-source/CurrentCompactCallerModelV1.lean:312`|
|M065|`AspisR1CurrentCaller.verifier.mark`|`CurrentCompactCallerModelV1`|`evidence/port17release-20261024/dependency-source/CurrentCompactCallerModelV1.lean:101`|
|M066|`AspisR1CurrentPreparedClaim.ClaimPowers.powers`|`CurrentClaimPowersInstance`|`docs/research/100bit-spend-path-20261013/lean-candidates/s1-claim-caller-composition-20261020/sources/CurrentClaimPowersInstance.lean:22`|
|M067|`AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.add`|`CurrentClaimSumModel`|`docs/research/100bit-spend-path-20261013/lean-candidates/s1-claim-parser-and-inner-trace-20261020/sources/CurrentClaimSumModel.lean:151`|
|M068|`AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.mul`|`CurrentClaimSumModel`|`docs/research/100bit-spend-path-20261013/lean-candidates/s1-claim-parser-and-inner-trace-20261020/sources/CurrentClaimSumModel.lean:154`|
|M069|`AspisR1CurrentPreparedClaim.trace.value`|`CurrentClaimSumModel`|`docs/research/100bit-spend-path-20261013/lean-candidates/s1-claim-parser-and-inner-trace-20261020/sources/CurrentClaimSumModel.lean:128`|
|M070|`AspisR1CurrentPreparedClaim.verifier.prepared_claim`|`CurrentClaimDotModel`|`docs/research/100bit-spend-path-20261013/lean-candidates/s1-claim-caller-composition-20261020/sources/CurrentClaimDotModel.lean:218`|
|M071|`AspisR1CurrentWide.field.CM31.add`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:34`|
|M072|`AspisR1CurrentWide.field.CM31.mul`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:151`|
|M073|`AspisR1CurrentWide.field.CM31.mul_m31`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:215`|
|M074|`AspisR1CurrentWide.field.CM31.sub`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:74`|
|M075|`AspisR1CurrentWide.field.M31.add`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:24`|
|M076|`AspisR1CurrentWide.field.M31.double`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:103`|
|M077|`AspisR1CurrentWide.field.M31.mul`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:141`|
|M078|`AspisR1CurrentWide.field.M31.reduce_u64`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:134`|
|M079|`AspisR1CurrentWide.field.M31.sub`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:63`|
|M080|`AspisR1CurrentWide.field.QM31.add`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:43`|
|M081|`AspisR1CurrentWide.field.QM31.mul`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:175`|
|M082|`AspisR1CurrentWide.field.QM31.mul_m31`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:224`|
|M083|`AspisR1CurrentWide.field.QM31.sub`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:83`|
|M084|`AspisR1CurrentWide.field.mul_by_r`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:108`|
|M085|`AspisR1CurrentWide.field.reduce_u64`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:117`|
|M086|`AspisR1CurrentWide.field.wide_exact.WideExact.add`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:52`|
|M087|`AspisR1CurrentWide.field.wide_exact.WideExact.mul`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:197`|
|M088|`AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:233`|
|M089|`AspisR1CurrentWide.field.wide_exact.WideExact.sub`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:92`|
|M090|`AspisR1CurrentWide.field.wide_exact.mul_u`|`AspisR1CurrentWide.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean:190`|
|M091|`AspisR1CurrentWideMul.field.QM31.sub`|`CurrentWideMulCanonical`|`docs/research/100bit-spend-path-20261013/evidence/s1-current-wide-mul-canonical-20261020/diagnostics/raw-generated/AspisR1CurrentWideMul/Funs.lean:25`|
|M092|`AspisR1CurrentWideMul.field.wide_exact.WideExact.mul`|`CurrentWideMulCanonical`|`docs/research/100bit-spend-path-20261013/evidence/s1-current-wide-mul-canonical-20261020/diagnostics/raw-generated/AspisR1CurrentWideMul/Funs.lean:40`|
|M093|`AspisR1CurrentWideMul.field.wide_exact.mul_u`|`CurrentWideMulCanonical`|`docs/research/100bit-spend-path-20261013/evidence/s1-current-wide-mul-canonical-20261020/diagnostics/raw-generated/AspisR1CurrentWideMul/Funs.lean:33`|
|M094|`AspisR1DecodeKFullV10.aspis_core.field.CM31.from_le_bytes`|`AspisR1DecodeKFullV10.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-decode-k-canonicality-20261018/AspisR1DecodeKFullV10/Funs.lean:83`|
|M095|`AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes`|`AspisR1DecodeKFullV10.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-decode-k-canonicality-20261018/AspisR1DecodeKFullV10/Funs.lean:71`|
|M096|`AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes`|`AspisR1DecodeKFullV10.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-decode-k-canonicality-20261018/AspisR1DecodeKFullV10/Funs.lean:132`|
|M097|`AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k`|`AspisR1DecodeKFullV10.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-decode-k-canonicality-20261018/AspisR1DecodeKFullV10/Funs.lean:264`|
|M098|`AspisR1DotPushLocal.canonical.Dot.push`|`AspisR1DotPushLocal.Funs`|`docs/research/100bit-spend-path-20261013/lean-candidates/dot-push-four-source-residues-20261020/sources/AspisR1DotPushLocal/Funs.lean:27`|
|M099|`AspisR1EbyKFinish.EbyKDot.finish`|`AspisR1EbyKFinish.Funs`|`docs/research/100bit-spend-path-20261013/lean-candidates/eby-k-finish-total-source-20261020/sources/AspisR1EbyKFinish/Funs.lean:131`|
|M100|`AspisR1EbyKFinish.canonical.Dot.finish`|`AspisR1EbyKFinish.Funs`|`docs/research/100bit-spend-path-20261013/lean-candidates/eby-k-finish-total-source-20261020/sources/AspisR1EbyKFinish/Funs.lean:110`|
|M101|`AspisR1EbyKFinish.canonical.Q.limbs`|`AspisR1EbyKFinish.Funs`|`docs/research/100bit-spend-path-20261013/lean-candidates/eby-k-finish-total-source-20261020/sources/AspisR1EbyKFinish/Funs.lean:103`|
|M102|`AspisR1EbyKFinish.canonical.reduce`|`AspisR1EbyKFinish.Funs`|`docs/research/100bit-spend-path-20261013/lean-candidates/eby-k-finish-total-source-20261020/sources/AspisR1EbyKFinish/Funs.lean:83`|
|M103|`AspisR1EbyKFinish.field.wide_exact.WideExact.from_limbs`|`AspisR1EbyKFinish.Funs`|`docs/research/100bit-spend-path-20261013/lean-candidates/eby-k-finish-total-source-20261020/sources/AspisR1EbyKFinish/Funs.lean:28`|
|M104|`AspisR1GammaCaller.sampler.gamma_sample`|`GammaCallerExplicitHelpers`|`docs/research/v8-r0-zk-20261009/lean/GammaCallerExplicitHelpers.lean:30`|
|M105|`AspisR1LoopPowers.field.WideExact.mul`|`LoopPowersCandidateModel`|`docs/research/100bit-spend-path-20261013/lean-candidates/s1-explicit-loop-powers-proved-candidate-20261020/sources/LoopPowersCandidateModel.lean:47`|
|M106|`AspisR1M31Inverse.field.M31.inv`|`SAQ_InverseExplicitMul`|`lean/SAQ_InverseExplicitMul.lean:59`|
|M107|`AspisR1M31Inverse.field.square_n`|`SAQ_InverseExplicitMul`|`lean/SAQ_InverseExplicitMul.lean:51`|
|M108|`AspisR1M31Parser.field.M31.from_le_bytes`|`R1ExtractedM31Parser`|`docs/research/100bit-spend-path-20261013/lean/ExtractedM31Parser.lean:27`|
|M109|`AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums`|`RPv_PoseidonPreparedSum3Source`|`evidence/replay-tops3-20261027/RPv_PoseidonPreparedSum3Source.lean:37`|
|M110|`AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared`|`RPv_PoseidonPreparedSum3Source`|`evidence/replay-tops3-20261027/RPv_PoseidonPreparedSum3Source.lean:151`|
|M111|`AspisR1Post25Sampler.field.CM31.new`|`AspisR1Post25Sampler.Funs`|`docs/research/v8-r0-zk-20261009/lean/AspisR1Post25Sampler/Funs.lean:24`|
|M112|`AspisR1Post25Sampler.field.WideExact.new`|`AspisR1Post25Sampler.Funs`|`docs/research/v8-r0-zk-20261009/lean/AspisR1Post25Sampler/Funs.lean:56`|
|M113|`AspisR1Post25Sampler.sampler.decode8`|`AspisR1Post25Sampler.Funs`|`docs/research/v8-r0-zk-20261009/lean/AspisR1Post25Sampler/Funs.lean:191`|
|M114|`AspisR1Post25Sampler.sampler.low_base_p_digits`|`AspisR1Post25Sampler.Funs`|`docs/research/v8-r0-zk-20261009/lean/AspisR1Post25Sampler/Funs.lean:178`|
|M115|`AspisR1Post25Sampler.sampler.ordinary_sample`|`AspisR1Post25Sampler.Funs`|`docs/research/v8-r0-zk-20261009/lean/AspisR1Post25Sampler/Funs.lean:210`|
|M116|`AspisR1Post25Sampler.sampler.qm31_div_pass`|`AspisR1Post25Sampler.Funs`|`docs/research/v8-r0-zk-20261009/lean/AspisR1Post25Sampler/Funs.lean:100`|
|M117|`AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p`|`AspisR1Post25SamplerIndexedAddSmallCandidate.Funs`|`docs/research/v8-r0-zk-20261009/lean/AspisR1Post25SamplerIndexedAddSmallCandidate/Funs.lean:60`|
|M118|`AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_le_bytes`|`AspisR1PrefixAggregateParser.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-prefix-aggregate-20261016/AspisR1PrefixAggregateParser/Funs.lean:154`|
|M119|`AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_limbs`|`AspisR1PrefixAggregateParser.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-prefix-aggregate-20261016/AspisR1PrefixAggregateParser/Funs.lean:103`|
|M120|`AspisR1PrefixAggregateParser.r1_wire.Prefix.parse`|`AspisR1PrefixAggregateParser.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-prefix-aggregate-20261016/AspisR1PrefixAggregateParser/Funs.lean:660`|
|M121|`AspisR1PrefixAggregateParser.r1_wire.parse_record`|`AspisR1PrefixAggregateParser.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-prefix-aggregate-20261016/AspisR1PrefixAggregateParser/Funs.lean:535`|
|M122|`AspisR1PrefixAggregateParser.r1_wire.parse_record_at`|`AspisR1PrefixAggregateParser.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-prefix-aggregate-20261016/AspisR1PrefixAggregateParser/Funs.lean:628`|
|M123|`AspisR1PrefixAggregateParser.r1_wire.row_shape`|`AspisR1PrefixAggregateParser.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-prefix-aggregate-20261016/AspisR1PrefixAggregateParser/Funs.lean:433`|
|M124|`AspisR1PrefixAggregateParser.r1_wire.validate_record_fields`|`AspisR1PrefixAggregateParser.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-prefix-aggregate-20261016/AspisR1PrefixAggregateParser/Funs.lean:522`|
|M125|`AspisR1PublicPreparation.FinishModel.circle_validated`|`S1SemanticFinishModelV1`|`evidence/port17release-20261024/dependency-source/S1SemanticFinishModelV1.lean:68`|
|M126|`AspisR1PublicPreparation.FinishModel.finish`|`S1SemanticFinishModelV1`|`evidence/port17release-20261024/dependency-source/S1SemanticFinishModelV1.lean:223`|
|M127|`AspisR1PublicPreparation.PreparedModel.scalar`|`ExtractedPreparedModel`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/ExtractedPreparedModel.lean:18`|
|M128|`AspisR1PublicPreparation.PreparedModel.scalar_k`|`ExtractedPreparedModel`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/ExtractedPreparedModel.lean:34`|
|M129|`AspisR1PublicPreparation.PreparedScratchModel.prepare`|`CurrentPreparedScratchModel`|`docs/research/100bit-spend-path-20261013/lean-candidates/s1-prepared-claim-carrier-bridge-20261020/sources/CurrentPreparedScratchModel.lean:15`|
|M130|`AspisR1PublicPreparation.QueriesModel.queries`|`ExtractedOpeningQueriesModel`|`docs/research/100bit-spend-path-20261013/lean/bridge-opening-queries-1b98-20261017/ExtractedOpeningQueriesModel.lean:47`|
|M131|`AspisR1PublicPreparation.S1SemanticCode.verify`|`S1SemanticCodeVerifyV1`|`evidence/sdk-child2-20261026/SdkD_085/sources/S1SemanticCodeVerifyV1.lean:16`|
|M132|`AspisR1PublicPreparation.aspis_core.field.CM31.new`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:47`|
|M133|`AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.private_public`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:889`|
|M134|`AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:1331`|
|M135|`AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:987`|
|M136|`AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:1000`|
|M137|`AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.semantic`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:933`|
|M138|`AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.withdrawal_public`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:911`|
|M139|`AspisR1PublicPreparation.r1_semantic.public_transcript`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:2749`|
|M140|`AspisR1PublicPreparation.r1_wire.Prefix.record`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:2033`|
|M141|`AspisR1PublicPreparation.r1_wire.Prefix.validated_record`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:2046`|
|M142|`AspisR1PublicPreparation.r1_wire.SemanticTranscript.impl.state`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:2847`|
|M143|`AspisR1PublicPreparation.r1_wire.SemanticTranscript.new`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:2681`|
|M144|`AspisR1PublicPreparation.r1_wire.SemanticTranscript.sample_block_validated`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:2061`|
|M145|`AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:2091`|
|M146|`AspisR1PublicPreparation.r1_wire.ValidatedRecord.impl.framed`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:2026`|
|M147|`AspisR1PublicPreparation.r1_wire.ValidatedRecord.impl.row`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:2020`|
|M148|`AspisR1PublicPreparation.r1_wire.begin`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:2119`|
|M149|`AspisR1PublicPreparation.sampler.qm31_digits`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:1997`|
|M150|`AspisR1PublicPreparation.sampler.qm31_div_pass`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:1919`|
|M151|`AspisR1PublicPreparation.sampler.qm31_sample`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:2007`|
|M152|`AspisR1PublicPreparation.trace.value`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:2868`|
|M153|`AspisR1PublicPreparation.transcript.Transcript.absorb`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:2805`|
|M154|`AspisR1PublicPreparation.transcript.Transcript.block`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:2824`|
|M155|`AspisR1PublicPreparation.transcript.Transcript.new`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:2783`|
|M156|`AspisR1PublicPreparation.transport.Variant.folds`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:2860`|
|M157|`AspisR1PublicPreparation.transport.Variant.tag`|`AspisR1PublicPreparation.Funs`|`docs/research/100bit-spend-path-20261013/lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Funs.lean:2774`|
|M158|`AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.private_public`|`AspisR1PublicSerializer.Funs`|`evidence/replay-dry3-20261026/RPz2_recovered/AspisR1PublicSerializer/Funs.lean:25`|
|M159|`AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes`|`AspisR1PublicSerializer.Funs`|`evidence/replay-dry3-20261026/RPz2_recovered/AspisR1PublicSerializer/Funs.lean:494`|
|M160|`AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields`|`AspisR1PublicSerializer.Funs`|`evidence/replay-dry3-20261026/RPz2_recovered/AspisR1PublicSerializer/Funs.lean:150`|
|M161|`AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier`|`AspisR1PublicSerializer.Funs`|`evidence/replay-dry3-20261026/RPz2_recovered/AspisR1PublicSerializer/Funs.lean:163`|
|M162|`AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.semantic`|`AspisR1PublicSerializer.Funs`|`evidence/replay-dry3-20261026/RPz2_recovered/AspisR1PublicSerializer/Funs.lean:96`|
|M163|`AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.withdrawal_public`|`AspisR1PublicSerializer.Funs`|`evidence/replay-dry3-20261026/RPz2_recovered/AspisR1PublicSerializer/Funs.lean:47`|
|M164|`AspisR1Qm31ArithmeticProbe.field.CM31.add`|`AspisR1Qm31ArithmeticProbe.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-qm31-arithmetic-20261015/AspisR1Qm31ArithmeticProbe/Funs.lean:86`|
|M165|`AspisR1Qm31ArithmeticProbe.field.CM31.mul`|`AspisR1Qm31ArithmeticProbe.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-qm31-arithmetic-20261015/AspisR1Qm31ArithmeticProbe/Funs.lean:104`|
|M166|`AspisR1Qm31ArithmeticProbe.field.CM31.sub`|`AspisR1Qm31ArithmeticProbe.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-qm31-arithmetic-20261015/AspisR1Qm31ArithmeticProbe/Funs.lean:95`|
|M167|`AspisR1Qm31ArithmeticProbe.field.M31.add`|`AspisR1Qm31ArithmeticProbe.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-qm31-arithmetic-20261015/AspisR1Qm31ArithmeticProbe/Funs.lean:42`|
|M168|`AspisR1Qm31ArithmeticProbe.field.M31.double`|`AspisR1Qm31ArithmeticProbe.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-qm31-arithmetic-20261015/AspisR1Qm31ArithmeticProbe/Funs.lean:80`|
|M169|`AspisR1Qm31ArithmeticProbe.field.M31.mul`|`AspisR1Qm31ArithmeticProbe.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-qm31-arithmetic-20261015/AspisR1Qm31ArithmeticProbe/Funs.lean:63`|
|M170|`AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64`|`AspisR1Qm31ArithmeticProbe.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-qm31-arithmetic-20261015/AspisR1Qm31ArithmeticProbe/Funs.lean:73`|
|M171|`AspisR1Qm31ArithmeticProbe.field.M31.sub`|`AspisR1Qm31ArithmeticProbe.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-qm31-arithmetic-20261015/AspisR1Qm31ArithmeticProbe/Funs.lean:52`|
|M172|`AspisR1Qm31ArithmeticProbe.field.QM31.add`|`AspisR1Qm31ArithmeticProbe.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-qm31-arithmetic-20261015/AspisR1Qm31ArithmeticProbe/Funs.lean:137`|
|M173|`AspisR1Qm31ArithmeticProbe.field.QM31.mul`|`AspisR1Qm31ArithmeticProbe.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-qm31-arithmetic-20261015/AspisR1Qm31ArithmeticProbe/Funs.lean:146`|
|M174|`AspisR1Qm31ArithmeticProbe.field.mul_by_r`|`AspisR1Qm31ArithmeticProbe.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-qm31-arithmetic-20261015/AspisR1Qm31ArithmeticProbe/Funs.lean:127`|
|M175|`AspisR1Qm31ArithmeticProbe.field.reduce_u64`|`AspisR1Qm31ArithmeticProbe.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-qm31-arithmetic-20261015/AspisR1Qm31ArithmeticProbe/Funs.lean:25`|
|M176|`AspisR1Qm31SamplerIndex.field.CM31.new`|`AspisR1Qm31SamplerIndex.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-qm31-index-sampler-20261016/AspisR1Qm31SamplerIndex/Funs.lean:26`|
|M177|`AspisR1Qm31SamplerIndex.sampler.qm31_digits`|`AspisR1Qm31SamplerIndex.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-qm31-index-sampler-20261016/AspisR1Qm31SamplerIndex/Funs.lean:145`|
|M178|`AspisR1Qm31SamplerIndex.sampler.qm31_div_pass`|`AspisR1Qm31SamplerIndex.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-qm31-index-sampler-20261016/AspisR1Qm31SamplerIndex/Funs.lean:67`|
|M179|`AspisR1Qm31SamplerIndex.sampler.qm31_sample`|`AspisR1Qm31SamplerIndex.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-qm31-index-sampler-20261016/AspisR1Qm31SamplerIndex/Funs.lean:155`|
|M180|`AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish`|`Query31UnrolledDriverFirstStop`|`docs/research/v8-r0-zk-20261009/lean/Query31UnrolledDriverFirstStop.lean:14`|
|M181|`AspisR1QueryGeometryActual.domain.FibreIndex.get`|`AspisR1QueryGeometryActual.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-fibre-point-extraction-20261019/extraction/Funs.lean:25`|
|M182|`AspisR1QueryGeometryActual.fast_domain.fibre_point`|`AspisR1QueryGeometryActual.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-fibre-point-extraction-20261019/extraction/Funs.lean:564`|
|M183|`AspisR1QueryGeometryActual.fast_domain.table_value`|`AspisR1QueryGeometryActual.Funs`|`docs/research/100bit-spend-path-20261013/evidence/session-b-fibre-point-extraction-20261019/extraction/Funs.lean:556`|
|M184|`AspisR1QueryScanUnrolled.r0_transcript.block_rank`|`QueryScanConcreteWordsDecoder`|`docs/research/v8-r0-zk-20261009/lean/QueryScanConcreteWordsDecoder.lean:56`|
|M185|`AspisR1QueryScanUnrolled.r0_transcript.query_words`|`QueryScanConcreteWordsDecoder`|`docs/research/v8-r0-zk-20261009/lean/QueryScanConcreteWordsDecoder.lean:84`|
|M186|`AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes`|`AspisR1RecordParser.Funs`|`evidence/debug-fmt-20261026/DFm_sources/AspisR1RecordParser/Funs.lean:147`|
|M187|`AspisR1RecordParser.field.wide_exact.WideExact.from_limbs`|`AspisR1RecordParser.Funs`|`evidence/debug-fmt-20261026/DFm_sources/AspisR1RecordParser/Funs.lean:96`|
|M188|`AspisR1RecordParser.r1_wire.parse_record`|`AspisR1RecordParser.Funs`|`evidence/debug-fmt-20261026/DFm_sources/AspisR1RecordParser/Funs.lean:478`|
|M189|`AspisR1RecordParser.r1_wire.row_shape`|`AspisR1RecordParser.Funs`|`evidence/debug-fmt-20261026/DFm_sources/AspisR1RecordParser/Funs.lean:376`|
|M190|`AspisR1RecordParser.r1_wire.validate_record_fields`|`AspisR1RecordParser.Funs`|`evidence/debug-fmt-20261026/DFm_sources/AspisR1RecordParser/Funs.lean:465`|
|M191|`AspisR1RowShape.r1_wire.row_shape`|`AspisR1RowShape.Funs`|`evidence/parse-sem-20261025/PSem-018/sources/AspisR1RowShape/Funs.lean:37`|
|M192|`AspisR1SelectedMaskProbe.field.CM31.add`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:213`|
|M193|`AspisR1SelectedMaskProbe.field.CM31.double`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:284`|
|M194|`AspisR1SelectedMaskProbe.field.CM31.mul`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:231`|
|M195|`AspisR1SelectedMaskProbe.field.CM31.mul_m31`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:275`|
|M196|`AspisR1SelectedMaskProbe.field.CM31.new`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:201`|
|M197|`AspisR1SelectedMaskProbe.field.CM31.square`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:255`|
|M198|`AspisR1SelectedMaskProbe.field.CM31.sub`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:222`|
|M199|`AspisR1SelectedMaskProbe.field.M31.add`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:144`|
|M200|`AspisR1SelectedMaskProbe.field.M31.double`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:189`|
|M201|`AspisR1SelectedMaskProbe.field.M31.mul`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:165`|
|M202|`AspisR1SelectedMaskProbe.field.M31.neg`|`AspisR1SelectedMaskProbe.Funs`|`evidence/replay-dry5-20261026/RPz4_SelectedMaskFuns.lean:322`|
|M203|`AspisR1SelectedMaskProbe.field.M31.reduce_u62`|`RPv_RawPoseidonExtensionSlice`|`evidence/replay-tops3-20261027/RPv_RawPoseidonExtensionSlice.lean:12`|
|M204|`AspisR1SelectedMaskProbe.field.M31.reduce_u64`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:182`|
|M205|`AspisR1SelectedMaskProbe.field.M31.sub`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:154`|
|M206|`AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:321`|
|M207|`AspisR1SelectedMaskProbe.field.QM31.add`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:561`|
|M208|`AspisR1SelectedMaskProbe.field.QM31.mul`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:579`|
|M209|`AspisR1SelectedMaskProbe.field.QM31.mul_m31`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:607`|
|M210|`AspisR1SelectedMaskProbe.field.QM31.square`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:595`|
|M211|`AspisR1SelectedMaskProbe.field.QM31.sub`|`RPv_EqualityValueSlice`|`evidence/replay-tops3-20261027/RPv_EqualityValueSlice.lean:21`|
|M212|`AspisR1SelectedMaskProbe.field.mul_by_r`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:337`|
|M213|`AspisR1SelectedMaskProbe.field.reduce_u64`|`AspisR1SelectedMaskProbe.Funs`|`docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe/Funs.lean:117`|
|M214|`AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_i`|`AspisR1SelectedMaskProbe.Funs`|`evidence/replay-dry5-20261026/RPz4_SelectedMaskFuns.lean:330`|
|M215|`AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_r`|`AspisR1SelectedMaskProbe.Funs`|`evidence/replay-dry5-20261026/RPz4_SelectedMaskFuns.lean:312`|
|M216|`AspisR1SelectedMaskProbe.state_only_hiding.mask_power_26`|`AspisR1SelectedMaskProbe.Funs`|`evidence/replay-dry5-20261026/RPz4_SelectedMaskFuns.lean:191`|
|M217|`AspisR1SelectedMaskProbe.state_only_hiding.mul_tower_basis`|`AspisR1SelectedMaskProbe.Funs`|`evidence/replay-dry5-20261026/RPz4_SelectedMaskFuns.lean:336`|
|M218|`AspisR1SelectedMaskProbe.state_only_hiding.selected_mask_linears`|`AspisR1SelectedMaskProbe.Funs`|`evidence/replay-dry5-20261026/RPz4_SelectedMaskFuns.lean:282`|
|M219|`AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value`|`AspisR1SelectedMaskProbe.Funs`|`evidence/replay-dry5-20261026/RPz4_SelectedMaskFuns.lean:593`|
|M220|`AspisR1SelectedMaskProbe.state_only_poseidon.extension_from_raw_limbs`|`RPv_RawPoseidonExtensionSlice`|`evidence/replay-tops3-20261027/RPv_RawPoseidonExtensionSlice.lean:18`|
|M221|`AspisR1SelectedWideViewV1.verifier.candidate.wide_view`|`SelectedWideViewFunsV1`|`docs/research/100bit-spend-path-20261013/lean-candidates/selected-wide-view-inactive-binding-20261020/sources/SelectedWideViewFunsV1.lean:149`|
|M222|`AspisR1SemanticCallExtraction.aspis_core.field.CM31.add`|`AspisR1SemanticCallExtraction.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-source-proof-loops-20261019/AspisR1SemanticCallExtraction/Funs.lean:97`|
|M223|`AspisR1SemanticCallExtraction.aspis_core.field.CM31.mul`|`AspisR1SemanticCallExtraction.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-source-proof-loops-20261019/AspisR1SemanticCallExtraction/Funs.lean:119`|
|M224|`AspisR1SemanticCallExtraction.aspis_core.field.CM31.sub`|`AspisR1SemanticCallExtraction.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-source-proof-loops-20261019/AspisR1SemanticCallExtraction/Funs.lean:108`|
|M225|`AspisR1SemanticCallExtraction.aspis_core.field.M31.add`|`AspisR1SemanticCallExtraction.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-source-proof-loops-20261019/AspisR1SemanticCallExtraction/Funs.lean:42`|
|M226|`AspisR1SemanticCallExtraction.aspis_core.field.M31.double`|`AspisR1SemanticCallExtraction.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-source-proof-loops-20261019/AspisR1SemanticCallExtraction/Funs.lean:90`|
|M227|`AspisR1SemanticCallExtraction.aspis_core.field.M31.mul`|`AspisR1SemanticCallExtraction.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-source-proof-loops-20261019/AspisR1SemanticCallExtraction/Funs.lean:69`|
|M228|`AspisR1SemanticCallExtraction.aspis_core.field.M31.reduce_u64`|`AspisR1SemanticCallExtraction.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-source-proof-loops-20261019/AspisR1SemanticCallExtraction/Funs.lean:82`|
|M229|`AspisR1SemanticCallExtraction.aspis_core.field.M31.sub`|`AspisR1SemanticCallExtraction.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-source-proof-loops-20261019/AspisR1SemanticCallExtraction/Funs.lean:55`|
|M230|`AspisR1SemanticCallExtraction.aspis_core.field.QM31.add`|`AspisR1SemanticCallExtraction.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-source-proof-loops-20261019/AspisR1SemanticCallExtraction/Funs.lean:162`|
|M231|`AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul`|`AspisR1SemanticCallExtraction.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-source-proof-loops-20261019/AspisR1SemanticCallExtraction/Funs.lean:173`|
|M232|`AspisR1SemanticCallExtraction.aspis_core.field.mul_by_r`|`AspisR1SemanticCallExtraction.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-source-proof-loops-20261019/AspisR1SemanticCallExtraction/Funs.lean:144`|
|M233|`AspisR1SemanticCallExtraction.aspis_core.field.reduce_u64`|`AspisR1SemanticCallExtraction.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-source-proof-loops-20261019/AspisR1SemanticCallExtraction/Funs.lean:25`|
|M234|`AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary`|`AspisR1SemanticCallExtraction.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-source-proof-loops-20261019/AspisR1SemanticCallExtraction/Funs.lean:220`|
|M235|`AspisR1SemanticCallExtraction.r1_semantic.semantic_value`|`AspisR1SemanticCallExtraction.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-source-proof-loops-20261019/AspisR1SemanticCallExtraction/Funs.lean:264`|
|M236|`AspisR1Stage2.verifier.candidate.query_loop`|`Port2_QuerySource`|`docs/research/100bit-spend-path-20261013/lean/Port2_QuerySource.lean:51`|
|M237|`AspisR1Stage2Accumulate.fast_pairing.EbyKDot.new`|`AspisR1Stage2Accumulate.Funs`|`docs/research/100bit-spend-path-20261013/lean-candidates/eby-k-constructor-and-source-push-20261020/worker-archives/constructor/lean/adapted/AspisR1Stage2Accumulate/Funs.lean:26`|
|M238|`AspisR1Stage2Accumulate.fast_pairing.canonical.Dot.new`|`AspisR1Stage2Accumulate.Funs`|`docs/research/100bit-spend-path-20261013/lean-candidates/eby-k-constructor-and-source-push-20261020/worker-archives/constructor/lean/adapted/AspisR1Stage2Accumulate/Funs.lean:19`|
|M239|`AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:113`|
|M240|`AspisR1TerminalDecoder.aspis_core.field.M31.to_le_bytes`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:123`|
|M241|`AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:171`|
|M242|`AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:154`|
|M243|`AspisR1TerminalDecoder.atomic_statement.unwrap_fixed_slice`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:163`|
|M244|`AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:294`|
|M245|`AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.first_canonical_byte`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:299`|
|M246|`AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:306`|
|M247|`AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:395`|
|M248|`AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_lane_transition_boxed_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:2470`|
|M249|`AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:2867`|
|M250|`AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:2548`|
|M251|`AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_transfer_statement_boxed_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:2780`|
|M252|`AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_withdrawal_statement_boxed_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:2856`|
|M253|`AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.statement_public_common`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:425`|
|M254|`AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.transition_kind`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:412`|
|M255|`AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:1144`|
|M256|`AspisR1TerminalDecoder.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:1531`|
|M257|`AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:992`|
|M258|`AspisR1TerminalDecoder.pool_v1.pair_terminal.exact`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:1272`|
|M259|`AspisR1TerminalDecoder.pool_v1.pair_terminal.validate_verified_afterstate`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:941`|
|M260|`AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pair_afterstate_boxed_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:1826`|
|M261|`AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pair_live_snapshot_boxed_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:2355`|
|M262|`AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pool_v1_pair_late_public_statement_boxed_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:2365`|
|M263|`AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:2089`|
|M264|`AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:733`|
|M265|`AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:1026`|
|M266|`AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:852`|
|M267|`AspisR1TerminalDecoder.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:769`|
|M268|`AspisR1TerminalDecoder.pool_v1.payment_relation.decode_common`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:2662`|
|M269|`AspisR1TerminalDecoder.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:2730`|
|M270|`AspisR1TerminalDecoder.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:2815`|
|M271|`AspisR1TerminalDecoder.pool_v1.payment_relation.digest_is_canonical`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:516`|
|M272|`AspisR1TerminalDecoder.pool_v1.payment_relation.encode_common`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:465`|
|M273|`AspisR1TerminalDecoder.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:666`|
|M274|`AspisR1TerminalDecoder.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:606`|
|M275|`AspisR1TerminalDecoder.pool_v1.payment_relation.require_header`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:2705`|
|M276|`AspisR1TerminalDecoder.pool_v1.payment_relation.transfer_common`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:633`|
|M277|`AspisR1TerminalDecoder.pool_v1.payment_relation.validate_common`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:543`|
|M278|`AspisR1TerminalDecoder.pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:639`|
|M279|`AspisR1TerminalDecoder.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:570`|
|M280|`AspisR1TerminalDecoder.pool_v1.payment_relation.withdrawal_common`|`AspisR1TerminalDecoder.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean:511`|
|M281|`AspisR1WeightsFieldCurrent.weights.field`|`WeightsFieldExplicitDecoder`|`docs/research/100bit-spend-path-20261013/evidence/stage2-weights-field-selector-20261020/raw-generated/Funs.lean:25`|
|M282|`AspisR1WideToBytesIndexedCandidate.field.wide_exact.WideExact.to_le_bytes`|`AspisR1WideToBytesIndexedCandidate.FunsNoResourceOptions`|`docs/research/100bit-spend-path-20261013/evidence/s5-to-bytes-indexed-proof-v1/candidate/generated/Funs.lean:36`|
|M283|`AspisR1WideToBytesIndexedCandidate.field.wide_exact.WideExact.to_limbs`|`AspisR1WideToBytesIndexedCandidate.FunsNoResourceOptions`|`docs/research/100bit-spend-path-20261013/evidence/s5-to-bytes-indexed-proof-v1/candidate/generated/Funs.lean:21`|
|M284|`AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes`|`AspisR1WideToBytesSource.Funs`|`docs/research/100bit-spend-path-20261013/evidence/s5-to-bytes-source-cut-v1/generated/AspisR1WideToBytesSource/Funs.lean:136`|
|M285|`AspisR1WideToBytesSource.field.wide_exact.WideExact.to_limbs`|`AspisR1WideToBytesSource.Funs`|`docs/research/100bit-spend-path-20261013/evidence/s5-to-bytes-source-cut-v1/generated/AspisR1WideToBytesSource/Funs.lean:62`|
|M286|`AspisR1WithdrawalCaller.aspis_core.field.M31.to_le_bytes`|`AspisR1WithdrawalCaller.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-withdrawal-caller-20261016/AspisR1WithdrawalCaller/Funs.lean:26`|
|M287|`AspisR1WithdrawalCaller.pool_v1.payment_relation.digest_is_canonical`|`AspisR1WithdrawalCaller.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-withdrawal-caller-20261016/AspisR1WithdrawalCaller/Funs.lean:115`|
|M288|`AspisR1WithdrawalCaller.pool_v1.payment_relation.encode_common`|`AspisR1WithdrawalCaller.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-withdrawal-caller-20261016/AspisR1WithdrawalCaller/Funs.lean:323`|
|M289|`AspisR1WithdrawalCaller.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1`|`AspisR1WithdrawalCaller.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-withdrawal-caller-20261016/AspisR1WithdrawalCaller/Funs.lean:412`|
|M290|`AspisR1WithdrawalCaller.pool_v1.payment_relation.validate_common`|`AspisR1WithdrawalCaller.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-withdrawal-caller-20261016/AspisR1WithdrawalCaller/Funs.lean:150`|
|M291|`AspisR1WithdrawalCaller.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1`|`AspisR1WithdrawalCaller.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-withdrawal-caller-20261016/AspisR1WithdrawalCaller/Funs.lean:218`|
|M292|`AspisR1WithdrawalCaller.pool_v1.payment_relation.withdrawal_common`|`AspisR1WithdrawalCaller.Funs`|`docs/research/100bit-spend-path-20261013/lean/extracted-withdrawal-caller-20261016/AspisR1WithdrawalCaller/Funs.lean:201`|
|M293|`AspisR1WithdrawalValidation.pool_v1.payment_relation.digest_is_canonical`|`AspisR1WithdrawalValidation.Funs`|`evidence/replay-dry3-20261026/RPz2_recovered/AspisR1WithdrawalValidation/Funs.lean:44`|
|M294|`AspisR1WithdrawalValidation.pool_v1.payment_relation.validate_common`|`AspisR1WithdrawalValidation.Funs`|`evidence/replay-dry3-20261026/RPz2_recovered/AspisR1WithdrawalValidation/Funs.lean:79`|
|M295|`AspisR1WithdrawalValidation.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1`|`AspisR1WithdrawalValidation.Funs`|`evidence/replay-dry3-20261026/RPz2_recovered/AspisR1WithdrawalValidation/Funs.lean:147`|
|M296|`AspisR1WithdrawalValidation.pool_v1.payment_relation.withdrawal_common`|`AspisR1WithdrawalValidation.Funs`|`evidence/replay-dry3-20261026/RPz2_recovered/AspisR1WithdrawalValidation/Funs.lean:130`|
|M297|`AspisR64Field.field.M31.inv`|`AspisV8R19.GuardedFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/GuardedFieldSlice.lean:107`|
|M298|`AspisR64Field.field.M31.mul`|`AspisV8R19.GuardedFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/GuardedFieldSlice.lean:36`|
|M299|`AspisR64Field.field.reduce_u64`|`AspisV8R19.GuardedFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/GuardedFieldSlice.lean:19`|
|M300|`AspisR64Field.field.square_n`|`AspisV8R19.GuardedFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/GuardedFieldSlice.lean:100`|
|M301|`AspisR65Field.field.M31.add`|`AspisV8R19.ComplexFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/ComplexFieldSlice.lean:120`|
|M302|`AspisR65Field.field.M31.inv`|`AspisV8R19.ComplexFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/ComplexFieldSlice.lean:139`|
|M303|`AspisR65Field.field.M31.mul`|`AspisV8R19.ComplexFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/ComplexFieldSlice.lean:49`|
|M304|`AspisR65Field.field.M31.neg`|`AspisV8R19.ComplexFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/ComplexFieldSlice.lean:130`|
|M305|`AspisR65Field.field.reduce_u64`|`AspisV8R19.ComplexFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/ComplexFieldSlice.lean:32`|
|M306|`AspisR65Field.field.square_n`|`AspisV8R19.ComplexFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/ComplexFieldSlice.lean:113`|
|M307|`AspisR66Field.field.M31.add`|`AspisV8R19.QuarticFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/QuarticFieldSlice.lean:128`|
|M308|`AspisR66Field.field.M31.inv`|`AspisV8R19.QuarticFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/QuarticFieldSlice.lean:171`|
|M309|`AspisR66Field.field.M31.mul`|`AspisV8R19.QuarticFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/QuarticFieldSlice.lean:57`|
|M310|`AspisR66Field.field.M31.neg`|`AspisV8R19.QuarticFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/QuarticFieldSlice.lean:149`|
|M311|`AspisR66Field.field.M31.reduce_u64`|`AspisV8R19.QuarticFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/QuarticFieldSlice.lean:158`|
|M312|`AspisR66Field.field.M31.sub`|`AspisV8R19.QuarticFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/QuarticFieldSlice.lean:138`|
|M313|`AspisR66Field.field.reduce_u64`|`AspisV8R19.QuarticFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/QuarticFieldSlice.lean:40`|
|M314|`AspisR66Field.field.square_n`|`AspisV8R19.QuarticFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/QuarticFieldSlice.lean:121`|
|M315|`AspisR72Sampler.field.CM31.add`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:363`|
|M316|`AspisR72Sampler.field.CM31.double`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:372`|
|M317|`AspisR72Sampler.field.CM31.inv`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:252`|
|M318|`AspisR72Sampler.field.CM31.inv_with`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:179`|
|M319|`AspisR72Sampler.field.CM31.mul`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:304`|
|M320|`AspisR72Sampler.field.CM31.neg`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:328`|
|M321|`AspisR72Sampler.field.CM31.new`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:409`|
|M322|`AspisR72Sampler.field.CM31.square`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:284`|
|M323|`AspisR72Sampler.field.CM31.sub`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:336`|
|M324|`AspisR72Sampler.field.M31.add`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:81`|
|M325|`AspisR72Sampler.field.M31.double`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:91`|
|M326|`AspisR72Sampler.field.M31.inv`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:229`|
|M327|`AspisR72Sampler.field.M31.mul`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:133`|
|M328|`AspisR72Sampler.field.M31.neg`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:170`|
|M329|`AspisR72Sampler.field.M31.reduce_u64`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:277`|
|M330|`AspisR72Sampler.field.M31.sub`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:97`|
|M331|`AspisR72Sampler.field.QM31.add`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:542`|
|M332|`AspisR72Sampler.field.QM31.is_zero`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:67`|
|M333|`AspisR72Sampler.field.QM31.mul`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:513`|
|M334|`AspisR72Sampler.field.QM31.square`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:378`|
|M335|`AspisR72Sampler.field.QM31.sub`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:533`|
|M336|`AspisR72Sampler.field.QM31.try_inv`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:345`|
|M337|`AspisR72Sampler.field.mul_by_r`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:107`|
|M338|`AspisR72Sampler.field.reduce_u64`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:116`|
|M339|`AspisR72Sampler.field.square_n`|`AspisR72Sampler.Funs`|`docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean:222`|
|M340|`AspisS1M31Embedding.aspis_core.field.CM31.Insts.Aspis_coreR0ScalarCodeField.from_m31`|`S1M31EmbeddingSourceV1`|`evidence/port17release-20261024/dependency-source/S1M31EmbeddingSourceV1.lean:163`|
|M341|`AspisS1M31Embedding.aspis_core.field.CM31.from_m31`|`S1M31EmbeddingSourceV1`|`evidence/port17release-20261024/dependency-source/S1M31EmbeddingSourceV1.lean:133`|
|M342|`AspisS1M31Embedding.aspis_core.field.QM31.from_cm31`|`S1M31EmbeddingSourceV1`|`evidence/port17release-20261024/dependency-source/S1M31EmbeddingSourceV1.lean:142`|
|M343|`AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.from_qm31`|`S1M31EmbeddingSourceV1`|`evidence/port17release-20261024/dependency-source/S1M31EmbeddingSourceV1.lean:104`|
|M344|`AspisS1M31Embedding.aspis_core.field.wide_exact.canonical_qm31`|`S1M31EmbeddingSourceV1`|`evidence/port17release-20261024/dependency-source/S1M31EmbeddingSourceV1.lean:82`|
|M345|`AspisS1NativeCompact.compact.compact_row`|`S1NativeCompactModelV1`|`evidence/port17release-20261024/dependency-source/S1NativeCompactModelV1.lean:73`|
|M346|`AspisS1NativeCompact.compact.expand_semantic`|`S1NativeCompactModelV1`|`evidence/port17release-20261024/dependency-source/S1NativeCompactModelV1.lean:234`|
|M347|`AspisS1NativeCompact.r1_wire.row_shape`|`S1NativeCompactModelV1`|`evidence/port17release-20261024/dependency-source/S1NativeCompactModelV1.lean:92`|
|M348|`AspisS6SourceCodec.aspis_core.field.M31.from_le_bytes`|`S6FullSourceCodecV1`|`evidence/port17release-20261024/dependency-source/S6FullSourceCodecV1.lean:64`|
|M349|`AspisS6SourceCodec.aspis_core.field.M31.to_le_bytes`|`S6FullSourceCodecV1`|`evidence/port17release-20261024/dependency-source/S6FullSourceCodecV1.lean:71`|
|M350|`AspisS6SourceCodec.aspis_statement.atomic_statement.encode_digest_canonical`|`S6FullSourceCodecV1`|`evidence/port17release-20261024/dependency-source/S6FullSourceCodecV1.lean:76`|
|M351|`FIn_WeightsExtract.field.CM31.add`|`FIn_WeightsFuns`|`lean/FIn_WeightsFuns.lean:80`|
|M352|`FIn_WeightsExtract.field.CM31.mul`|`FIn_WeightsFuns`|`lean/FIn_WeightsFuns.lean:98`|
|M353|`FIn_WeightsExtract.field.CM31.sub`|`FIn_WeightsFuns`|`lean/FIn_WeightsFuns.lean:89`|
|M354|`FIn_WeightsExtract.field.M31.add`|`FIn_WeightsFuns`|`lean/FIn_WeightsFuns.lean:36`|
|M355|`FIn_WeightsExtract.field.M31.double`|`FIn_WeightsFuns`|`lean/FIn_WeightsFuns.lean:74`|
|M356|`FIn_WeightsExtract.field.M31.mul`|`FIn_WeightsFuns`|`lean/FIn_WeightsFuns.lean:57`|
|M357|`FIn_WeightsExtract.field.M31.reduce_u64`|`FIn_WeightsFuns`|`lean/FIn_WeightsFuns.lean:67`|
|M358|`FIn_WeightsExtract.field.M31.sub`|`FIn_WeightsFuns`|`lean/FIn_WeightsFuns.lean:46`|
|M359|`FIn_WeightsExtract.field.QM31.add`|`FIn_WeightsFuns`|`lean/FIn_WeightsFuns.lean:145`|
|M360|`FIn_WeightsExtract.field.QM31.mul`|`FIn_WeightsFuns`|`lean/FIn_WeightsFuns.lean:163`|
|M361|`FIn_WeightsExtract.field.QM31.sub`|`FIn_WeightsFuns`|`lean/FIn_WeightsFuns.lean:154`|
|M362|`FIn_WeightsExtract.field.mul_by_r`|`FIn_WeightsFuns`|`lean/FIn_WeightsFuns.lean:121`|
|M363|`FIn_WeightsExtract.field.reduce_u64`|`FIn_WeightsFuns`|`lean/FIn_WeightsFuns.lean:19`|
|M364|`FIo_Native.aspis_core.field.CM31.add`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:148`|
|M365|`FIo_Native.aspis_core.field.CM31.double`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:660`|
|M366|`FIo_Native.aspis_core.field.CM31.mul`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:269`|
|M367|`FIo_Native.aspis_core.field.CM31.mul_m31`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:424`|
|M368|`FIo_Native.aspis_core.field.CM31.square`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:637`|
|M369|`FIo_Native.aspis_core.field.CM31.sub`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:297`|
|M370|`FIo_Native.aspis_core.field.M31.add`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:133`|
|M371|`FIo_Native.aspis_core.field.M31.double`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:189`|
|M372|`FIo_Native.aspis_core.field.M31.mul`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:254`|
|M373|`FIo_Native.aspis_core.field.M31.reduce_u64`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:244`|
|M374|`FIo_Native.aspis_core.field.M31.sub`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:198`|
|M375|`FIo_Native.aspis_core.field.QM31.add`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:161`|
|M376|`FIo_Native.aspis_core.field.QM31.mul`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:310`|
|M377|`FIo_Native.aspis_core.field.QM31.mul_m31`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:437`|
|M378|`FIo_Native.aspis_core.field.QM31.square`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:723`|
|M379|`FIo_Native.aspis_core.field.QM31.sub`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:330`|
|M380|`FIo_Native.aspis_core.field.mul_by_r`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:213`|
|M381|`FIo_Native.aspis_core.field.reduce_u64`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:225`|
|M382|`FIo_Native.aspis_core.field.wide_exact.WideExact.add`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:175`|
|M383|`FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:540`|
|M384|`FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:466`|
|M385|`FIo_Native.aspis_core.field.wide_exact.WideExact.mul`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:353`|
|M386|`FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:451`|
|M387|`FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:409`|
|M388|`FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:520`|
|M389|`FIo_Native.aspis_core.field.wide_exact.canonical_qm31`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:387`|
|M390|`FIo_Native.aspis_core.field.wide_exact.mul_u`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:342`|
|M391|`FIo_Native.aspis_core.r0.heap.filled`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:816`|
|M392|`FIo_Native.fast_pairing.EbyKDot.finish`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:1276`|
|M393|`FIo_Native.fast_pairing.EbyKDot.new`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:1241`|
|M394|`FIo_Native.fast_pairing.EbyKDot.push`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:1248`|
|M395|`FIo_Native.fast_pairing.canonical.Dot.finish`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:1199`|
|M396|`FIo_Native.fast_pairing.canonical.Dot.new`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:1141`|
|M397|`FIo_Native.fast_pairing.canonical.Dot.push`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:1187`|
|M398|`FIo_Native.fast_pairing.canonical.Q.from_limbs`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:1092`|
|M399|`FIo_Native.fast_pairing.canonical.Q.from_wide`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:1120`|
|M400|`FIo_Native.fast_pairing.canonical.Q.limbs`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:1114`|
|M401|`FIo_Native.fast_pairing.canonical.reduce`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:1072`|
|M402|`FIo_Native.fast_pairing.checked_q`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:1228`|
|M403|`FIo_Native.fast_pairing.limbs_of`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:1218`|
|M404|`FIo_Native.trace.value`|`FIo_NativeFuns`|`lean/FIo_NativeFuns.lean:1300`|
|M405|`FIq_Native.field.CM31.add`|`RPu_FIq_Native01`|`evidence/replay-tops2-20261027/RPu_FIq_Native01.lean:187`|
|M406|`FIq_Native.field.CM31.double`|`RPu_FIq_Native01`|`evidence/replay-tops2-20261027/RPu_FIq_Native01.lean:258`|
|M407|`FIq_Native.field.CM31.from_m31`|`RPu_FIq_Native01`|`evidence/replay-tops2-20261027/RPu_FIq_Native01.lean:181`|
|M408|`FIq_Native.field.CM31.mul`|`RPu_FIq_Native01`|`evidence/replay-tops2-20261027/RPu_FIq_Native01.lean:205`|
|M409|`FIq_Native.field.CM31.mul_m31`|`RPu_FIq_Native01`|`evidence/replay-tops2-20261027/RPu_FIq_Native01.lean:249`|
|M410|`FIq_Native.field.CM31.new`|`RPu_FIq_Native01`|`evidence/replay-tops2-20261027/RPu_FIq_Native01.lean:175`|
|M411|`FIq_Native.field.CM31.square`|`RPu_FIq_Native01`|`evidence/replay-tops2-20261027/RPu_FIq_Native01.lean:229`|
|M412|`FIq_Native.field.CM31.sub`|`RPu_FIq_Native01`|`evidence/replay-tops2-20261027/RPu_FIq_Native01.lean:196`|
|M413|`FIq_Native.field.M31.add`|`RPu_FIq_Native01`|`evidence/replay-tops2-20261027/RPu_FIq_Native01.lean:118`|
|M414|`FIq_Native.field.M31.double`|`RPu_FIq_Native01`|`evidence/replay-tops2-20261027/RPu_FIq_Native01.lean:163`|
|M415|`FIq_Native.field.M31.mul`|`RPu_FIq_Native01`|`evidence/replay-tops2-20261027/RPu_FIq_Native01.lean:139`|
|M416|`FIq_Native.field.M31.reduce_u62`|`RPu_FIq_Native01`|`evidence/replay-tops2-20261027/RPu_FIq_Native01.lean:149`|
|M417|`FIq_Native.field.M31.reduce_u64`|`RPu_FIq_Native01`|`evidence/replay-tops2-20261027/RPu_FIq_Native01.lean:156`|
|M418|`FIq_Native.field.M31.sub`|`RPu_FIq_Native01`|`evidence/replay-tops2-20261027/RPu_FIq_Native01.lean:128`|
|M419|`FIq_Native.field.PreparedQm31Multiplier.new`|`RPu_FIq_Native01`|`evidence/replay-tops2-20261027/RPu_FIq_Native01.lean:295`|
|M420|`FIq_Native.field.QM31.add`|`RPu_FIq_Native02`|`evidence/replay-tops2-20261027/RPu_FIq_Native02.lean:44`|
|M421|`FIq_Native.field.QM31.from_cm31`|`RPu_FIq_Native02`|`evidence/replay-tops2-20261027/RPu_FIq_Native02.lean:38`|
|M422|`FIq_Native.field.QM31.mul`|`RPu_FIq_Native02`|`evidence/replay-tops2-20261027/RPu_FIq_Native02.lean:62`|
|M423|`FIq_Native.field.QM31.mul_m31`|`RPu_FIq_Native02`|`evidence/replay-tops2-20261027/RPu_FIq_Native02.lean:90`|
|M424|`FIq_Native.field.QM31.square`|`RPu_FIq_Native02`|`evidence/replay-tops2-20261027/RPu_FIq_Native02.lean:78`|
|M425|`FIq_Native.field.QM31.sub`|`RPu_FIq_Native02`|`evidence/replay-tops2-20261027/RPu_FIq_Native02.lean:53`|
|M426|`FIq_Native.field.mul_by_r`|`RPu_FIq_Native01`|`evidence/replay-tops2-20261027/RPu_FIq_Native01.lean:311`|
|M427|`FIq_Native.field.qm31_from_karatsuba_channel_sums`|`RPu_FIq_Native01`|`evidence/replay-tops2-20261027/RPu_FIq_Native01.lean:386`|
|M428|`FIq_Native.field.qm31_m31_dot`|`RPu_FIq_Native02`|`evidence/replay-tops2-20261027/RPu_FIq_Native02.lean:351`|
|M429|`FIq_Native.field.qm31_pack_base4`|`RPu_FIq_Native02`|`evidence/replay-tops2-20261027/RPu_FIq_Native02.lean:107`|
|M430|`FIq_Native.field.qm31_sum_products3_prepared`|`RPu_FIq_Native02`|`evidence/replay-tops2-20261027/RPu_FIq_Native02.lean:9`|
|M431|`FIq_Native.field.reduce_u64`|`RPu_FIq_Native01`|`evidence/replay-tops2-20261027/RPu_FIq_Native01.lean:91`|
|M432|`FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors.active`|`RPu_FIq_Native13`|`evidence/replay-tops2-20261027/RPu_FIq_Native13.lean:225`|
|M433|`FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors.at_point`|`RPu_FIq_Native14`|`evidence/replay-tops2-20261027/RPu_FIq_Native14.lean:149`|
|M434|`FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point`|`RPu_FIq_Native14`|`evidence/replay-tops2-20261027/RPu_FIq_Native14.lean:167`|
|M435|`FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors.expand`|`RPu_FIq_Native14`|`evidence/replay-tops2-20261027/RPu_FIq_Native14.lean:136`|
|M436|`FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors.row`|`RPu_FIq_Native08`|`evidence/replay-tops2-20261027/RPu_FIq_Native08.lean:267`|
|M437|`FIq_Native.pool_v1.pair_forest_copy_terminal.copy_residual`|`RPu_FIq_CopyPrefix`|`evidence/replay-tops2-20261027/RPu_FIq_CopyPrefix.lean:94`|
|M438|`FIq_Native.pool_v1.pair_forest_copy_terminal.evaluate_with_selectors`|`RPu_FIq_Native14`|`evidence/replay-tops2-20261027/RPu_FIq_Native14.lean:51`|
|M439|`FIq_Native.pool_v1.pair_forest_copy_terminal.lift_m31`|`RPu_FIq_CopyPrefix`|`evidence/replay-tops2-20261027/RPu_FIq_CopyPrefix.lean:8`|
|M440|`FIq_Native.pool_v1.pair_forest_copy_terminal.link_weight`|`RPu_FIq_CopyPrefix`|`evidence/replay-tops2-20261027/RPu_FIq_CopyPrefix.lean:56`|
|M441|`FIq_Native.pool_v1.pair_forest_copy_terminal.pattern_values`|`RPu_FIq_Native13`|`evidence/replay-tops2-20261027/RPu_FIq_Native13.lean:113`|
|M442|`FIq_Native.pool_v1.pair_forest_semantic_terminal.add_occupancy_lanes`|`RPu_FIq_Native09`|`evidence/replay-tops2-20261027/RPu_FIq_Native09.lean:108`|
|M443|`FIq_Native.pool_v1.pair_forest_semantic_terminal.add_path_lanes`|`RPu_FIq_Native10`|`evidence/replay-tops2-20261027/RPu_FIq_Native10.lean:114`|
|M444|`FIq_Native.pool_v1.pair_forest_semantic_terminal.add_preweighted`|`RPu_FIq_Native09`|`evidence/replay-tops2-20261027/RPu_FIq_Native09.lean:77`|
|M445|`FIq_Native.pool_v1.pair_forest_semantic_terminal.add_schedule_lanes`|`RPu_FIq_Native10`|`evidence/replay-tops2-20261027/RPu_FIq_Native10.lean:393`|
|M446|`FIq_Native.pool_v1.pair_forest_semantic_terminal.add_value_lanes`|`RPu_FIq_Native09`|`evidence/replay-tops2-20261027/RPu_FIq_Native09.lean:352`|
|M447|`FIq_Native.pool_v1.pair_forest_semantic_terminal.bounded_append_carry`|`RPu_FIq_Native08`|`evidence/replay-tops2-20261027/RPu_FIq_Native08.lean:261`|
|M448|`FIq_Native.pool_v1.pair_forest_semantic_terminal.composition_parts`|`RPu_FIq_Native14`|`evidence/replay-tops2-20261027/RPu_FIq_Native14.lean:219`|
|M449|`FIq_Native.pool_v1.pair_forest_semantic_terminal.copy_variant`|`RPu_FIq_Native08`|`evidence/replay-tops2-20261027/RPu_FIq_Native08.lean:34`|
|M450|`FIq_Native.pool_v1.pair_forest_semantic_terminal.empty_root`|`RPu_FIq_Native08`|`evidence/replay-tops2-20261027/RPu_FIq_Native08.lean:231`|
|M451|`FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value`|`RPu_FIq_Native14`|`evidence/replay-tops2-20261027/RPu_FIq_Native14.lean:365`|
|M452|`FIq_Native.pool_v1.pair_forest_semantic_terminal.initial_variant_selectors`|`RPu_FIq_Native10`|`evidence/replay-tops2-20261027/RPu_FIq_Native10.lean:295`|
|M453|`FIq_Native.pool_v1.pair_forest_semantic_terminal.lift_m31`|`RPu_FIq_Native08`|`evidence/replay-tops2-20261027/RPu_FIq_Native08.lean:79`|
|M454|`FIq_Native.pool_v1.pair_forest_semantic_terminal.poseidon_selectors`|`RPu_FIq_Native11`|`evidence/replay-tops2-20261027/RPu_FIq_Native11.lean:67`|
|M455|`FIq_Native.pool_v1.pair_forest_semantic_terminal.private_public`|`RPu_FIq_Native03`|`evidence/replay-tops2-20261027/RPu_FIq_Native03.lean:56`|
|M456|`FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.semantic`|`RPu_FIq_Native03`|`evidence/replay-tops2-20261027/RPu_FIq_Native03.lean:78`|
|M457|`FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31`|`RPu_FIq_Native14`|`evidence/replay-tops2-20261027/RPu_FIq_Native14.lean:417`|
|M458|`FIq_Native.pool_v1.pair_forest_semantic_terminal.reconstruct_10`|`RPu_FIq_Native09`|`evidence/replay-tops2-20261027/RPu_FIq_Native09.lean:245`|
|M459|`FIq_Native.pool_v1.pair_forest_semantic_terminal.scalar_lanes`|`RPu_FIq_Native08`|`evidence/replay-tops2-20261027/RPu_FIq_Native08.lean:48`|
|M460|`FIq_Native.pool_v1.pair_forest_semantic_terminal.selected_claim`|`RPu_FIq_Native07`|`evidence/replay-tops2-20261027/RPu_FIq_Native07.lean:205`|
|M461|`FIq_Native.pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption`|`RPu_FIq_Native10`|`evidence/replay-tops2-20261027/RPu_FIq_Native10.lean:311`|
|M462|`FIq_Native.pool_v1.pair_forest_semantic_terminal.semantic_packed`|`RPu_FIq_Native11`|`evidence/replay-tops2-20261027/RPu_FIq_Native11.lean:8`|
|M463|`FIq_Native.pool_v1.pair_forest_semantic_terminal.sum_high`|`RPu_FIq_Native10`|`evidence/replay-tops2-20261027/RPu_FIq_Native10.lean:101`|
|M464|`FIq_Native.pool_v1.pair_forest_semantic_terminal.terminal_parts`|`RPu_FIq_Native14`|`evidence/replay-tops2-20261027/RPu_FIq_Native14.lean:379`|
|M465|`FIq_Native.pool_v1.pair_forest_semantic_terminal.validate_transition`|`RPu_FIq_Native11`|`evidence/replay-tops2-20261027/RPu_FIq_Native11.lean:188`|
|M466|`FIq_Native.pool_v1.pair_forest_semantic_terminal.variant_expected_output`|`RPu_FIq_Native08`|`evidence/replay-tops2-20261027/RPu_FIq_Native08.lean:445`|
|M467|`FIq_Native.pool_v1.pair_forest_semantic_terminal.withdrawal_public`|`RPu_FIq_Native03`|`evidence/replay-tops2-20261027/RPu_FIq_Native03.lean:34`|
|M468|`FIq_Native.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected`|`RPu_FIq_Native07`|`evidence/replay-tops2-20261027/RPu_FIq_Native07.lean:146`|
|M469|`FIq_Native.state_only_poseidon.extension_from_raw_limbs`|`RPu_FIq_Native04`|`evidence/replay-tops2-20261027/RPu_FIq_Native04.lean:261`|
|M470|`FIq_Native.state_only_poseidon.extension_limbs`|`RPu_FIq_Native04`|`evidence/replay-tops2-20261027/RPu_FIq_Native04.lean:277`|
|M471|`FIq_Native.state_only_poseidon.external_linear_lazy`|`RPu_FIq_Native06`|`evidence/replay-tops2-20261027/RPu_FIq_Native06.lean:341`|
|M472|`FIq_Native.state_only_poseidon.external_linear_packed`|`RPu_FIq_Native05`|`evidence/replay-tops2-20261027/RPu_FIq_Native05.lean:423`|
|M473|`FIq_Native.state_only_poseidon.external_local_packed`|`RPu_FIq_Native05`|`evidence/replay-tops2-20261027/RPu_FIq_Native05.lean:389`|
|M474|`FIq_Native.state_only_poseidon.external_local_packed_raw`|`RPu_FIq_Native05`|`evidence/replay-tops2-20261027/RPu_FIq_Native05.lean:323`|
|M475|`FIq_Native.state_only_poseidon.full_round`|`RPu_FIq_Native06`|`evidence/replay-tops2-20261027/RPu_FIq_Native06.lean:377`|
|M476|`FIq_Native.state_only_poseidon.full_round_m31_constants`|`RPu_FIq_Native07`|`evidence/replay-tops2-20261027/RPu_FIq_Native07.lean:92`|
|M477|`FIq_Native.state_only_poseidon.full_round_m31_constants_packed`|`RPu_FIq_Native07`|`evidence/replay-tops2-20261027/RPu_FIq_Native07.lean:56`|
|M478|`FIq_Native.state_only_poseidon.full_round_packed`|`RPu_FIq_Native05`|`evidence/replay-tops2-20261027/RPu_FIq_Native05.lean:463`|
|M479|`FIq_Native.state_only_poseidon.internal_linear_lazy`|`RPu_FIq_Native04`|`evidence/replay-tops2-20261027/RPu_FIq_Native04.lean:357`|
|M480|`FIq_Native.state_only_poseidon.internal_round`|`RPu_FIq_Native04`|`evidence/replay-tops2-20261027/RPu_FIq_Native04.lean:388`|
|M481|`FIq_Native.state_only_poseidon.interpolate_three_constant_columns`|`RPu_FIq_Native05`|`evidence/replay-tops2-20261027/RPu_FIq_Native05.lean:74`|
|M482|`FIq_Native.state_only_poseidon.interpolate_three_constant_limb`|`RPu_FIq_Native05`|`evidence/replay-tops2-20261027/RPu_FIq_Native05.lean:8`|
|M483|`FIq_Native.state_only_poseidon.interpolated_full_pair_packed`|`RPu_FIq_Native07`|`evidence/replay-tops2-20261027/RPu_FIq_Native07.lean:8`|
|M484|`FIq_Native.state_only_poseidon.interpolated_internal_pair`|`RPu_FIq_Native04`|`evidence/replay-tops2-20261027/RPu_FIq_Native04.lean:400`|
|M485|`FIq_Native.state_only_poseidon.leading_pair_packed`|`RPu_FIq_Native07`|`evidence/replay-tops2-20261027/RPu_FIq_Native07.lean:129`|
|M486|`FIq_Native.state_only_poseidon.pow5`|`RPu_FIq_Native04`|`evidence/replay-tops2-20261027/RPu_FIq_Native04.lean:381`|
|M487|`MultiproofParserRef.reference.check_values`|`MultiproofParserRef.Funs`|`docs/research/100bit-spend-path-20261013/lean/MultiproofParserRef/Funs.lean:167`|
|M488|`Op3I_Source.transport.Variant.tag`|`Op3I_Source`|`lean/Op3I_Source.lean:105`|
|M489|`Op3I_Source.verifier.candidate.parse_shape`|`Op3I_Source`|`lean/Op3I_Source.lean:337`|
|M490|`Op4P_Extract.Op4P_reference.canonical_scan`|`Op4P_Extract.Funs`|`lean/Op4P_Extract/Funs.lean:237`|
|M491|`Op4P_Extract.Op4P_reference.reference.check_values`|`Op4P_Extract.Funs`|`lean/Op4P_Extract/Funs.lean:97`|
|M492|`OraclePortCkptAbi2Extracted.aspis_core.field.M31.to_le_bytes`|`OraclePortCkptAbi2Extracted.Funs`|`docs/research/100bit-spend-path-20261013/lean/OraclePortCkptAbi2Extracted/Funs.lean:102`|
|M493|`OraclePortCkptAbi2Extracted.aspis_core.field.wide_exact.WideExact.from_limbs`|`OraclePortCkptAbi2Extracted.Funs`|`docs/research/100bit-spend-path-20261013/lean/OraclePortCkptAbi2Extracted/Funs.lean:29`|
|M494|`OraclePortCkptAbi2Extracted.aspis_core.field.wide_exact.WideExact.to_limbs`|`OraclePortCkptAbi2Extracted.Funs`|`docs/research/100bit-spend-path-20261013/lean/OraclePortCkptAbi2Extracted/Funs.lean:83`|
|M495|`S8Kani2MutableExtraction.aspis_core.field.M31.reduce_u64`|`S8Kani2MutableSource`|`docs/research/100bit-spend-path-20261013/lean/S8Kani2MutableSource.lean:95`|
|M496|`S8Kani2MutableExtraction.aspis_core.field.reduce_u64`|`S8Kani2MutableSource`|`docs/research/100bit-spend-path-20261013/lean/S8Kani2MutableSource.lean:78`|
|M497|`S8Kani2MutableExtraction.batched_weights.BatchedWeights.finish`|`S8Kani2MutableSource`|`docs/research/100bit-spend-path-20261013/lean/S8Kani2MutableSource.lean:261`|
|M498|`S8OwnedP6.aspis_core.field.CM31.from_le_bytes`|`S8OwnedP6.Funs`|`docs/research/100bit-spend-path-20261013/lean/S8OwnedP6/Funs.lean:116`|
|M499|`S8OwnedP6.aspis_core.field.M31.from_le_bytes`|`S8OwnedP6.Funs`|`docs/research/100bit-spend-path-20261013/lean/S8OwnedP6/Funs.lean:104`|
|M500|`S8OwnedP6.aspis_core.field.M31.reduce_u64`|`S8OwnedP6.Funs`|`docs/research/100bit-spend-path-20261013/lean/S8OwnedP6/Funs.lean:94`|
|M501|`S8OwnedP6.aspis_core.field.QM31.from_le_bytes`|`S8OwnedP6.Funs`|`docs/research/100bit-spend-path-20261013/lean/S8OwnedP6/Funs.lean:156`|
|M502|`S8OwnedP6.aspis_core.field.reduce_u64`|`S8OwnedP6.Funs`|`docs/research/100bit-spend-path-20261013/lean/S8OwnedP6/Funs.lean:75`|
|M503|`V7Tag73CurrentHelpersOpaque.aspis_core.field.M31.inv`|`AspisV8R19.InverseFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/InverseFieldSlice.lean:78`|
|M504|`V7Tag73CurrentHelpersOpaque.aspis_core.field.M31.mul`|`AspisV8R19.InverseFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/GeneratedM31Mul.lean:9`|
|M505|`V7Tag73CurrentHelpersOpaque.aspis_core.field.reduce_u64`|`AspisV8R19.InverseFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/CurrentFieldSlice.lean:55`|
|M506|`V7Tag73CurrentHelpersOpaque.aspis_core.field.square_n`|`AspisV8R19.InverseFieldSlice`|`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/InverseFieldSlice.lean:71`|
|M507|`WAdm_Fissioned.aspis_core.field.wide_exact.WideExact.to_le_bytes`|`RPz7_WAdm_Fissioned_FunsExternal`|`evidence/replay-dry8-20261026/RPz7_WAdm_Fissioned_FunsExternal.lean:16`|

## Validation, receipts and retained boundaries

No Lean compile (0/30), Kani run (0), Rust execution/build (0), SBF rebuild or
frozen-manifest replay was launched. No new top theorem exists; `#print axioms`
is N/A for this job. The retained replay declaration audits are reused evidence,
not new kernel checks. No host scope, admission attempt, shared workspace,
Aeneas library object, persistent cache or session A file was touched; therefore
no host/cache start/end mutation or reservation receipt exists. No shipped file
or cfg(kani) harness changed; the ELF rebuild trigger did not fire. No hash is
claimed newly reproduced.

Inherited pins:

- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

`NBI1_VALIDATE.json` and `NBI1_validation-time.txt` record exact static target,
exit, wall, peak RSS, swaps, worker/source revisions, source/closure hashes and
axioms N/A. `NBI1_validate.py` independently rehashes every selected frozen
span, checks all model names and owner receipts,13 leaf boundaries, callee
coverage and bottom-up ordering. These checks validate this inventory; they
are not formal source-to-model refinement. `NBI1_SOURCE_FILES.json` seals the
270 inspected file hashes. The rest of crates/programs/Cargo.lock is also
checked byte-identical to the frozen revision by git diff.

The Python inventory parser uses tree-sitter0.25.2 / tree-sitter-rust0.24.2.
An initial tree-sitter0.26 parser segfault and one diagnostic rerun led to that
parser version pin; no prover was involved. A slow first cohort scan was stopped
and replaced with a stricter scan keyed to retained modules plus canonical Lean
sources. Own assembler defects (forward unit reference, audit count versus list)
were repaired before validation. The first independent validation found an unresolved private-Q callee inside the stopped Dot.push leaf; its owner was made explicit and the failed receipt is retained as NBI1_validation-failed1-*.txt. No failed script result is credited as evidence.
Intermediate AST/cohort indices are reproducible scratch outputs, not retained
proof caches. The stage2 call graph is superseded by NBI1_INVENTORY.json.

Exact claim: a frozen-source static TX1 inventory and cohort-name/owner mapping,
plus proposed bridge cuts and domains. Assumptions discharged/added/changed:
none. Existing library, runtime/ABI, allocator, extraction, digest/oracle,
query-budget and source-to-ELF boundaries remain. This does not close enclosing
S2, D188 caller association or the100-bit target. The next concrete work is the
native release-dispatch/snapshot/decoder-to-owned wrapper bridge, followed
bottom-up by parser/prepare/batch/query/flush domain composition into the SAME
checkpoint writer. Every CLOSED leaf is reused within its existing domain.

All stage commits are local; no push, merge, key/wallet operation, other worker
prefix edit or compiler/cache cleanup occurred.
