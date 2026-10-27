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
