# Aspis translatability pass: verifier crate and on-chain program adapter

Status: target not yet established. This note records, for every function of
`crates/aspis-r1-cost-probe` and `programs/r1-cost-probe` that the Aspis
one-transaction entry reaches under the deployed feature set, whether the
Charon and Aeneas tools translate it and whether the emitted Lean elaborates,
and the source changes proposed where they do not. It is a tool record. Nothing
here is a proof, and a translated function is not a verified function.

Scope given by the lead: program entry, pool-adapter route, `stage2_owned`
one-transaction block, `fused::verify_summed_format` and everything these
call inside the two crates. Not in scope: `crates/aspis-statement`,
`crates/aspis-core`, `crates/aspis-prover`, `programs/aspis-pool`,
`prover.rs`, `RealR1_client.rs`, and `sampler::low_base_p_digits` and
`sampler::add_small_base_p` (rewritten by the lead). Calls into the two
library crates are boundaries here.

Result in brief (2026-11-12). Two patches against the base tree `src-base2`,
in `translatability/verifier/patches/`:

- patch 0, `tp1-p0-restore-pinned-text.patch` (sha256
  8a8f3f1e66964aab221d051043d2a116385b92e803af260be4a51b0963ab2779): the
  pinned text of twelve R1 functions that the experiment had edited, with the
  Aspis form as a separate definition under `#[cfg]`. Gate `tp1-p0d`: all
  gates pass; 3 compute units less than the base on every measured case.
- the batch, `tp1-b1-translatability.patch` (sha256
  a353f3d796dd4bcf7abf1e571ec95fb4151eab70bab371190e70ddb7bcae522b): the
  translatability rewrites. Gate `tp1-f3` on the final tree: all gates pass;
  187 compute units more than the base on the two recorded payments, 178 to
  190 on the six worst-case scenarios.

Release-style emission of the final tree with the second tool pair (Aeneas
with `-abort-on-error`, exit 0 for both crates): of 257 function rows, 250
translate and their Lean elaborates against the R1 library, 1 translates and
does not elaborate (`compact::expand_values`: library models missing), 6 are
opaque named gaps of the program crate (`close_checkpoint`, the three
lifecycle functions, the two program-id statics). Sections 5 and 6. Function
text against the pin on the final tree: 710 identical, 11 identical under an
added `#[cfg]`, 10 changed, 83 not at the pin. Section 1.

Sections 1 and 2 describe the head before any patch; sections 3 and 4 the two
patches and their gates; section 5 the final emission; section 6 what remains
and why.

## 1. Binding rule and what was checked first

The soundness lead's rule: an R1 function that the Aspis build still compiles
and calls, and whose row in the on-chain status table
(`ONCHAIN-PATH-EXTRACTION-STATUS-20261111.md` on `origin/research`, read
with `git show`) is settled or translatable as is, keeps text byte-identical
to c7593d23fdc. An alternative selected by a deployed feature is a separate
definition under `#[cfg]`. Rewrites are for rows whose column (c) says yes,
for rows whose model is a rewritten crate (adopt that text), and for functions
that exist only in Aspis.

Function-by-function text comparison (`tools/TP_fntext.py`: every `fn` of
every `.rs` file of the two crates that exists at the pin, text from its first
attribute line to its closing brace):

| Compared | identical | identical under an added cfg attribute | changed | not present at the pin |
|---|---|---|---|---|
| c7593d23fdc against the head ea0e8bd91c3 | 718 | 0 | 13 | 42 |
| c7593d23fdc against the base tree `src-base2` with patch 0 (third version) | 716 | 12 | 3 | 63 |
| c7593d23fdc against the final tree (base tree + patch 0 + the batch) | 710 | 11 | 10 | 83 |

The 13 functions changed at the head: `batch_tree`, `canonical_scan`
(candidate.rs); `EbyKDot::push` (fast_pairing.rs); `semantic_boundary`,
`semantic_value` (r1_semantic.rs); `validate_record_fields`,
`ValidatedRecord::decode_k` (r1_wire.rs); `prepared_claim` (verifier.rs);
`process_r1_cost_probe_instruction` (lib.rs); `scan_proof_buffer`
(r1_pool_adapter.rs); `stage1`, `stage2`, `stage2_owned`
(r1_pool_adapter_owned.rs). Eleven were changed by the experiment commits; two
(`semantic_value`, `decode_k`) by the extraction rewrites of 7dffe3e2a93, of
which `decode_k` has column (c) yes and `semantic_value` has column (c) no
(the rewrite of `semantic_value` broke the rule; patch 0 puts the pinned text
back). The comparison covers functions only: constants, types and trait
declarations are not compared. One file of the verifier crate, `fused.rs`,
does not exist at the pin and is left out of these counts.

After patch 0 three functions are still changed against the pin:
`sampler::low_base_p_digits` and `sampler::add_small_base_p` (rewritten by
the lead in the base tree) and `prepared_claim` (left to the batch, see
section 3). In the final tree ten are changed: those three, and
`canonical_scan`, `wide_view`, `claims`, `Prepared::new`,
`QueryGeometry::for_range`, `authenticate_asq8_accounts`,
`decode_lane_from_pool_release`, all rewritten by the batch (section 4). The
eleven functions identical under an added `#[cfg]` attribute in the final
tree are `batch_tree`, `EbyKDot::push`, `semantic_boundary`,
`semantic_value`, `validate_record_fields`, `decode_k`,
`process_r1_cost_probe_instruction`, `stage1`, `stage2`, `stage2_owned`,
`scan_proof_buffer`. Every other function that exists at the pin has
byte-identical text (710).

Patch 0, `patches/tp1-p0-restore-pinned-text.patch` (third version, sha256
8a8f3f1e66964aab221d051043d2a116385b92e803af260be4a51b0963ab2779, made with
`diff -ruN` against `src-base2`, built by `tools/TP_restore.py`; the two
earlier versions failed their gates and are kept under
`patches/superseded/`, see section 3): each of twelve of the 13 gets its
pinned text back under `#[cfg(not(feature))]`, and what the Aspis or
experimental configuration compiles becomes a second definition of the same
name under `#[cfg(feature)]`, marked "Aspis new gate; equality with the
pinned function is owed". Switches: `future-lean-parse`
(validate_record_fields), `future-word-scan` (canonical_scan),
`future-lean-dot` (EbyKDot::push), `future-lazy-boundary`
(semantic_boundary), `future-lazy-horner` (semantic_value),
`future-validated-decode` (decode_k), `future-merkle-single-pass`
(batch_tree), `future-one-tx` (scan_proof_buffer, stage2, stage2_owned),
`future-one-tx-lean` (stage1); `process_r1_cost_probe_instruction` has the
pinned text when `pool-adapter` is on and the experiment's measurement entry
otherwise. The two helpers that held a pinned body
(`validate_record_fields_pinned`, `canonical_scan_pinned`) remain as test
oracles under `#[cfg(test)]`. The thirteenth, `prepared_claim`, is not
touched by patch 0: it is a rewrite candidate, the batch replaces it, and
restoring its pinned text first costs compute (section 3).

`future-lazy-horner` was a feature of aspis-core and of the program crate
only; a crate cannot test another crate's feature, so the patch gives the
verifier crate a feature of that name which turns the aspis-core one on, and
the program's feature turns both on. Every build of the verifier crate that
is meant to be the deployed configuration must name `future-lazy-horner` and
not `aspis-core/future-lazy-horner`: with the latter alone the pinned
`semantic_value` is compiled.

## 2. Classification at the head

Source: the head ea0e8bd91c3 (host tree `src-xp1`, checked equal to the head
on the sixteen files in scope). Deployed feature set, exactly: verifier crate
`private-leaf-salts,optimized-terminal,program-build,future-validated-decode,future-merkle-single-pass,future-merkle-in-place,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-fold-shared,aspis-core/future-fast-kmul,aspis-core/future-fast-prepared,aspis-core/future-fast-square,aspis-core/future-lazy-horner`,
overflow checks on; program crate the list of `fv_round7.sh`, overflow checks
off (as the program is built).

Runs (all through `fv_slot.sh`, receipts `TP-*`): verifier crate, root
`verify_summed_format`, nothing in the crate opaque: Charon `TP-C01` (527
functions in the output), Aeneas `TP-A01`, Lean `TP-L01`, `TP-L02`.
Program crate, root `process_r1_cost_probe_instruction`: Charon `TP-C02`,
Aeneas `TP-A02`, Lean `TP-L03`. First pair: program crate `TP-C03`,
`TP-A03`; five R1 functions of the verifier crate `TP-C04`, `TP-A04`.
Aeneas ran without `-abort-on-error` so that one pass lists every rejection.
"Elaborates" means against the R1 (L187) library with the header change, the
copied library definitions of `extraction-probe/lean/AspisXPNewLib.lean`,
and one naming rule: where a parameter or local is called `compact` or
`weights`, the emitted reference to an item of the module of the same name
is written with its full name (R1's own gate module does the same).

Tool pair. The second pair (Charon 454586e9, Aeneas 0d21a9ec) is the one to
use for the release emission of both crates. The first pair (Charon daad69be,
Aeneas b59d5188-lean432-extended) stops on an uncaught `Not_found`
(InterpReduceCollapse.ml:1991) on both scopes, rejects `stage2`,
`close_checkpoint` and `lifecycle_accounts` ("Instantiating the type
parameters of a function with types containing mutable borrows is currently
not allowed"), and rejects `wide_view` with the same message as the second
pair. No function was found that the first pair translates and the second
does not; for `canonical_scan`, `QueryGeometry::for_range`, `prepare`
and `verify_observed` the first pair gave no verdict because the run stopped.

Counts over the 271 functions the two emissions reach (second pair):
234 translate and elaborate,
9 translate but the Lean does not
elaborate, 24 do not translate, 4
are boundaries of the scope they appear in (items of the verifier crate seen
from the program crate).

What does not translate, by cause:

- function-pointer type (`Observer`): `verify_summed_format`, `fold_sums`,
  `summed_final_checks` (Aspis only); `verifier::mark`, `prepare`,
  `r1_semantic::mark`, `verify_finish`, `verify_observed` (R1);
  `observer` (program);
- loops: `prepared_claim` ("Returns inside of nested loops"),
  `require_distinct_accounts` (same), `decode_lane_from_pool_release`
  ("Early returns inside of loops"), `canonical_scan`'s pinned body
  ("Continue to outer loops"), `QueryGeometry::for_range` ("Could not match
  the contexts"), `deployment_ids::program_id` ("Early returns inside of
  loops");
- slice pattern over accounts: `authenticate_asq8_accounts`,
  `close_checkpoint`, `lifecycle_accounts` ("Inconsistent projection");
- other: `Prepared::new` ("Unreachable"), `wide_view` ("There should be no
  bottoms in the value"), `claims` ("Joining region abstractions…"; it also
  writes through raw pointers), `deployment_id` and the two program-id
  constants ("Internal error").

Three of these are R1 functions whose row says the frozen function extracts
(column (c) no) and which neither pair translated in these runs:
`canonical_scan`, `QueryGeometry::for_range`, `wide_view`. Under the
binding rule they keep their text; how R1's gate modules for them were
produced is not something these runs reproduce. This is an open finding. (The
soundness lead then ruled the three to be rewrite candidates, because their
rows are not settled; they are rewritten in the batch, section 4.)

What translates but does not elaborate: `base_lanes_tight` and `stage2`
(two library definitions the R1 library lacks and the second pair's own
library has: indexing by a full range, and `&mut [T]` to `&mut [T; N]`);
`compact::expand_values` (no model of the mutable chunk iterator);
`authenticate_invariant_release_registry` (array inequality: a type mismatch
in the emitted call); `lifecycle_init`, `lifecycle_write`,
`lifecycle_finalize` (they depend on `lifecycle_accounts`); the two sampler
functions the lead has since rewritten. Also failing, as declarations without
a function row: the instances emitted for `M31::reduce_u64` passed as a
value to array `map` (used by `semantic_boundary`'s Aspis form and
`k_of`).

Not reached. 80 of the 218 rows the status table has for the two
crates name functions that Charon does not reach from the two roots under the
deployed features (reachability is over the code before constant branches are
removed, so it errs towards reaching more):

- `candidate.rs`: `slot`, `batch_keys`, `sort_batch_keys`, `same_batch_leaf`, `same_batch_index`, `batch_key_at`, `batch_merkle`, `batch_merkle_values`, `batch_tree`, `query_values`, `query_loop`, `tx1`, `tx2_common`, `tx2_authenticated`
- `compact.rs`: `slot_offset`
- `fast_dots.rs`: `four_dots_one`, `four_dots`
- `fast_pairing.rs`: `pair`, `reduce_pair`, `Q::add`, `Q::sub`, `Q::mul_m31`, `Q::mul`, `Q::square`
- `lib.rs`: `first_decoded`
- `multiproof.rs`: `Arity::bits`, `Arity::width`, `Arity::levels`, `well_formed`, `index_at`, `value_at`, `root_matches`, `occupied_binary_parent`, `sibling_binary_parent`, `node_count`, `verify_in_place`
- `r1_pool_adapter_owned.rs`: `require_zero`, `stage1_owned`
- `r1_wire.rs`: `statement_points`
- `transport.rs`: `Variant::final_len`, `Variant::row`
- `verifier.rs`: `circle_fold_with_inverses`, `line_fold_with_inverses`, `BatchedWeights::push`, `BatchedWeights::value`, `BatchedWeights::finish`, `residue_limb_at`, `power_limb_at`, `update_residue_row`, `basis_at`, `accumulated_weight_at`, `accumulate_batched_with_node`, `finish_query_dot`, `finish_relation`, `put`, `put_k`, `checkpoint`, `Reader::raw`, `Reader::e`, `Reader::k`, `validate_checkpoint_queries`, `read_checkpoint_weights`, `read_checkpoint_semantic_alpha`, `resume`
- `weights.rs`: `kpowers`, `s2_grouped_inactive_pair`, `grouped_inactive_pair`, `twofold_libra_weights`, `shared_two_point_guard`, `push_byte_products`, `partial_dot`, `high_dot`, `process_regular_kinds`, `shared_partials`, `shared_high`, `process_kind`, `Weights::raw`, `Weights::tensor`, `Weights::pair`, `Weights::dense_point_pair`

So the two-transaction code (`tx1`, `tx2_*`, `query_values`,
`query_loop`, `batch_*`, `verify_in_place`, `finish_relation`, the
checkpoint writers and readers, `stage1_owned`, `first_decoded`) is not on
the Aspis path. `close_checkpoint` and the `lifecycle_*` functions ARE
reached, through `process`.

### Table

One row per function reached. "R1 row" quotes columns (b) and (c) of the
status table; "new gate" means the function does not exist at the pin.
"Text identical" is at the head, before patch 0.

| Function | Source | Second pair | Lean (second-pair emission) | First pair | R1 row | Text identical to c7593d23fdc |
|---|---|---|---|---|---|---|
| `verifier::candidate::fused::verify_summed_format` | fused.rs:None | NO: Arrow types are not supported yet |  | not run | new gate | not present at the pin |
| `verifier::mark` | verifier.rs:None | NO: Arrow types are not supported yet; Function pointers are not supported yet |  | not run | (b) CANNOT-EXTRACT (PCXN_CANNOT_EXTRACT.json CE07): arrow types. Key Curre | (c) yes | yes |
| `verifier::candidate::prepare` | candidate.rs:None | NO: Arrow types are not supported yet |  | not run | (b) EXTRACTED gate (NMP_prepare `prepare` OPEN; CurrentCompactCallerModelV; NOT SETTLED | (c) yes (through CE03 callee) | yes |
| `verifier::candidate::fused::fold_sums` | fused.rs:None | NO: Arrow types are not supported yet |  | not run | new gate | not present at the pin |
| `verifier::candidate::fused::summed_final_checks` | fused.rs:None | NO: Arrow types are not supported yet |  | not run | new gate | not present at the pin |
| `r1_semantic::verify_observed` | r1_semantic.rs:None | NO: Arrow types are not supported yet |  | not run | (b) EXTRACTED: NMP_prepare.Funs; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `r1_semantic::mark` | r1_semantic.rs:None | NO: Arrow types are not supported yet |  | not run | (b) Observer call (release: None). No key. It shares the arrow-type constr | (c) likely yes (arrow type); record silent | yes |
| `r1_semantic::verify_finish` | r1_semantic.rs:None | NO: Arrow types are not supported yet |  | not run | (b) EXTRACTED: NNG_verify_finish `verify_finish` OPEN; its Types are OPEN_; NOT SETTLED | (c) yes (through CE11-CE13 callees) | yes |
| `program::observer` | lib.rs:None | NO: Arrow types are not supported yet |  | not run | (b) EXTRACTED: AdapterRwModel `AdapterRw.observer` CONDITIONAL_ON_BINDING;; NOT SETTLED | (c) no | yes |
| `verifier::candidate::opening` | candidate.rs:29 | translates | elaborates | not run | (b) EXTRACTED: NJS_Extract.Funs; SETTLED | (c) no | yes |
| `verifier::candidate::parse_shape` | candidate.rs:40 | axiom (opaque or body rejected) |  | not run | (b) EXTRACTED: NJS_Extract.Funs, NJS_Extract.Types, Op3I_Source | (c) no (the frozen function extracts; what r | yes |
| `verifier::candidate::canonical_scan` | candidate.rs:54 | translates | elaborates | not run | (b) EXTRACTED: NJS_Extract.Funs | (c) no (the frozen function extracts; what r | no |
| `verifier::candidate::canonical_scan_words::limbs_ok::ONES` | candidate.rs:74 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::canonical_scan_words::limbs_ok::HIGHS` | candidate.rs:75 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::canonical_scan_words::limbs_ok` | candidate.rs:77 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::canonical_scan_words` | candidate.rs:87 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::canonical_scan_pinned` | candidate.rs:95 | NO: Continue to outer loops are not supported yet |  | not run | new gate | not present at the pin |
| `verifier::candidate::wide_view` | candidate.rs:117 | NO: There should be no bottoms in the value |  | NO: There should be no bottoms in the value | (b) EXTRACTED: SelectedWideViewFunsV1; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `verifier::candidate::batch_leaf` | candidate.rs:158 | translates | elaborates | not run | (b) EXTRACTED: NJS_Extract.Funs | (c) no (the frozen function extracts; what r | yes |
| `verifier::candidate::merkle_verdict` | candidate.rs:283 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::HEADER` | compact.rs:26 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::QUERIES` | compact.rs:28 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::SEMANTIC_ROWS` | compact.rs:29 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::LOGICAL_SEMANTIC` | compact.rs:31 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::SEMANTIC_COMPACT_VALUES` | compact.rs:33 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::COMPACT_SEMANTIC` | compact.rs:34 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::COMPACT_Y1` | compact.rs:35 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::LOGICAL_Y1` | compact.rs:36 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::OPENING` | compact.rs:37 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::OFF_SEMANTIC` | compact.rs:38 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::OFF_Y1` | compact.rs:39 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::OFF_INACTIVE` | compact.rs:40 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::OFF_ROUND0` | compact.rs:41 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::OFF_FOLDED_ROOT` | compact.rs:42 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::OFF_ROUND1` | compact.rs:43 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::OFF_FINAL` | compact.rs:44 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::FINAL_LEN` | compact.rs:45 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::OFF_OPENINGS` | compact.rs:46 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::OFF_NODES` | compact.rs:47 | translates | elaborates | not run | new gate | not present at the pin |
| `compact::compact_row` | compact.rs:80 | translates | elaborates | not run | (b) EXTRACTED: S1NativeCompactModelV1; SETTLED | (c) no | yes |
| `compact::expand_values` | compact.rs:131 | translates | error: Unknown constant `core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice` | not run | (b) HAND MODEL / RECONSTRUCTED: S1ValuesOwnedModelV1 (owned-Vec index loop | (c) no (it extracts; library models missing) | yes |
| `compact::check_values` | compact.rs:140 | translates | elaborates | not run | (b) Gate counterpart S8OwnedP6 check_values_owned (OPEN; ownership/signatu; NOT SETTLED | (c) not established | yes |
| `compact::expand_semantic` | compact.rs:154 | translates | elaborates | not run | (b) EXTRACTED: S1NativeCompactModelV1 | (c) no (the frozen function extracts; what r | yes |
| `program::r1_pool_adapter::deployment_ids::program_id` | deployment_ids.rs:3 | NO: Early returns inside of loops are not supported yet |  | not run | no row | yes |
| `program::r1_pool_adapter::deployment_ids::program_id::ALPHABET` | deployment_ids.rs:4 | translates | elaborates | not run | new gate | not present at the pin |
| `program::r1_pool_adapter::deployment_ids::deployment_id` | deployment_ids.rs:46 | NO: Internal error, please file an issue |  | not run | no row | yes |
| `fast_domain::TABLE_A` | fast_domain.rs:13 | translates | elaborates | not run | new gate | not present at the pin |
| `fast_domain::TABLE_B` | fast_domain.rs:144 | translates | elaborates | not run | new gate | not present at the pin |
| `fast_domain::table_value` | fast_domain.rs:276 | translates | elaborates | not run | (b) EXTRACTED: AspisR1QueryGeometryActual.Funs, NFN_ExtractedGeometry; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `fast_domain::fibre_point` | fast_domain.rs:282 | translates | elaborates | not run | (b) EXTRACTED: AspisR1QueryGeometryActual.Funs, NFN_ExtractedGeometry; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `fast_domain::line_node` | fast_domain.rs:295 | translates | elaborates | not run | (b) EXTRACTED: NFN_ExtractedGeometry | (c) no (the frozen function extracts; what r | yes |
| `fast_pairing::canonical::P` | fast_pairing.rs:5 | translates | elaborates | not run | new gate | not present at the pin |
| `fast_pairing::canonical::reduce` | fast_pairing.rs:10 | translates | elaborates | not run | (b) OPEN GAP: no key in the 1,707-key universe and no constant of this nam | (c) not established | yes |
| `fast_pairing::canonical::{fast_pairing::canonical::Q}::from_limbs` | fast_pairing.rs:24 | translates | elaborates | not run | (b) EXTRACTED: EbyKPushExplicitTypesV1, RPz7_FIo_NativeFuns; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `fast_pairing::canonical::{fast_pairing::canonical::Q}::limbs` | fast_pairing.rs:29 | translates | elaborates | not run | (b) EXTRACTED: RPz7_FIo_NativeFuns; SETTLED | (c) no | yes |
| `fast_pairing::canonical::{fast_pairing::canonical::Q}::from_wide` | fast_pairing.rs:33 | translates | elaborates | not run | (b) EXTRACTED: RPz7_FIo_NativeFuns | (c) no (the frozen function extracts; what r | yes |
| `fast_pairing::canonical::{fast_pairing::canonical::Q}::raw` | fast_pairing.rs:82 | translates | elaborates | not run | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `fast_pairing::canonical::{fast_pairing::canonical::Q}::raw::PP` | fast_pairing.rs:85 | translates | elaborates | not run | new gate | not present at the pin |
| `fast_pairing::canonical::{fast_pairing::canonical::Dot}::new` | fast_pairing.rs:112 | translates | elaborates | not run | (b) EXTRACTED: RPz7_FIo_NativeFuns; SETTLED | (c) no | yes |
| `fast_pairing::canonical::{fast_pairing::canonical::Dot}::push` | fast_pairing.rs:118 | translates | elaborates | not run | (b) EXTRACTED: RPz7_FIo_NativeFuns; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `fast_pairing::canonical::{fast_pairing::canonical::Dot}::finish` | fast_pairing.rs:123 | translates | elaborates | not run | (b) EXTRACTED: RPz7_FIo_NativeFuns; SETTLED | (c) no | yes |
| `fast_pairing::canonical::{fast_pairing::canonical::Dot}::value` | fast_pairing.rs:125 | translates | elaborates | not run | new gate | not present at the pin |
| `fast_pairing::canonical::{fast_pairing::canonical::Dot}::push_limbs` | fast_pairing.rs:132 | translates | elaborates | not run | new gate | not present at the pin |
| `fast_pairing::canonical::{fast_pairing::canonical::Dot}::push_limbs::PP` | fast_pairing.rs:133 | translates | elaborates | not run | new gate | not present at the pin |
| `fast_pairing::MAX_TERMS` | fast_pairing.rs:149 | translates | elaborates | not run | new gate | not present at the pin |
| `fast_pairing::limbs_of` | fast_pairing.rs:152 | translates | elaborates | not run | (b) EXTRACTED: RPz7_FIo_NativeFuns; SETTLED | (c) no | yes |
| `fast_pairing::checked_q` | fast_pairing.rs:157 | translates | elaborates | not run | (b) EXTRACTED: RPz7_FIo_NativeFuns; SETTLED | (c) no | yes |
| `fast_pairing::qm31_of` | fast_pairing.rs:162 | translates | elaborates | not run | (b) OPEN GAP: no key in the 1,707-key universe and no constant of this nam | (c) not established | yes |
| `fast_pairing::{fast_pairing::EbyKDot}::new` | fast_pairing.rs:179 | translates | elaborates | not run | (b) EXTRACTED: RPz7_FIo_NativeFuns; SETTLED | (c) no | yes |
| `fast_pairing::{fast_pairing::EbyKDot}::push` | fast_pairing.rs:184 | translates | elaborates | not run | (b) EXTRACTED: RPz7_FIo_NativeFuns; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `fast_pairing::{fast_pairing::EbyKDot}::push_lean` | fast_pairing.rs:203 | translates | elaborates | not run | new gate | not present at the pin |
| `fast_pairing::{fast_pairing::EbyKDot}::finish` | fast_pairing.rs:211 | translates | elaborates | not run | (b) EXTRACTED: RPz7_FIo_NativeFuns; SETTLED | (c) no | yes |
| `fast_pairing::{fast_pairing::EbyKDot}::value` | fast_pairing.rs:220 | translates | elaborates | not run | new gate | not present at the pin |
| `fast_pairing::{fast_pairing::KbyKDot}::new` | fast_pairing.rs:278 | translates | elaborates | not run | (b) EXTRACTED: RPz7_FIo_NativeFuns; SETTLED | (c) no | yes |
| `fast_pairing::{fast_pairing::KbyKDot}::push` | fast_pairing.rs:283 | translates | elaborates | not run | (b) EXTRACTED: RPz7_FIo_NativeFuns; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `fast_pairing::{fast_pairing::KbyKDot}::push_lean` | fast_pairing.rs:299 | translates | elaborates | not run | new gate | not present at the pin |
| `fast_pairing::{fast_pairing::KbyKDot}::finish` | fast_pairing.rs:307 | translates | elaborates | not run | (b) EXTRACTED: RPz7_FIo_NativeFuns; SETTLED | (c) no | yes |
| `fast_pairing::{fast_pairing::KbyKDot}::value` | fast_pairing.rs:313 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::P64` | fused.rs:26 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::NO_BYTES` | fused.rs:87 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::relation_view` | fused.rs:88 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::coefficients` | fused.rs:132 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::extension_lane` | fused.rs:200 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::push_k4` | fused.rs:219 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::push_e4` | fused.rs:226 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::push_e` | fused.rs:232 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::finish_e4` | fused.rs:236 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::first_fold_base` | fused.rs:242 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::first_fold_extension` | fused.rs:250 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::second_fold` | fused.rs:259 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::cubic` | fused.rs:293 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::k_of` | fused.rs:364 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::base_query` | fused.rs:381 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::base_fold` | fused.rs:408 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::base_accumulate` | fused.rs:415 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::base_lanes_tight` | fused.rs:433 | translates | error: Unknown identifier `core.slice.index.SliceIndexRangeFullSlice` | not run | new gate | not present at the pin |
| `verifier::candidate::fused::CERTIFICATE_BYTES` | fused.rs:522 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::ROW_CLAIMS` | fused.rs:523 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::ROW_ROUND` | fused.rs:524 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::final_rounds` | fused.rs:593 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::final_message_at` | fused.rs:607 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::claims_bytes` | fused.rs:613 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::equality_tables` | fused.rs:628 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::query_weight_mle_pairs` | fused.rs:680 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::summed_format::MAGIC` | fused.rs:778 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::summed_format::SLOT_NODES` | fused.rs:781 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::summed_format::OFF_NODES` | fused.rs:782 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::summed_format::slot_offset` | fused.rs:786 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::summed_format::OFF_CERTIFICATE` | fused.rs:792 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::summed_format::PROOF_BYTES` | fused.rs:793 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::parse_shape_summed` | fused.rs:800 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::merged_keys` | fused.rs:815 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::merged_tree` | fused.rs:837 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::candidate::fused::merged_merkle` | fused.rs:857 | translates | elaborates | not run | new gate | not present at the pin |
| `program::{impl aspis_core::digest::Digest32 for program::SolanaDigest}` | lib.rs:11 | translates | elaborates | not run | new gate | not present at the pin |
| `program::{impl aspis_core::digest::Digest32 for program::SolanaDigest}::digest` | lib.rs:13 | translates | elaborates | not run | no row | yes |
| `program::{impl aspis_core::digest::Digest32 for program::SolanaDigest}::digest_into` | lib.rs:20 | translates | elaborates | not run | new gate | not present at the pin |
| `program::error` | lib.rs:55 | translates | elaborates | not run | no row | yes |
| `program::process_r1_cost_probe_instruction` | lib.rs:71 | translates | elaborates | not run | (b) Entry point. With `pool-adapter` only the adapter arm is compiled: `po | (c) no for the emission; it is uncompiled fo | no |
| `multiproof::LEAF_BITS` | multiproof.rs:18 | translates | elaborates | not run | new gate | not present at the pin |
| `multiproof::BINARY_NODE_TAG` | multiproof.rs:21 | translates | elaborates | not run | new gate | not present at the pin |
| `multiproof::MAX_MERGED` | multiproof.rs:300 | translates | elaborates | not run | new gate | not present at the pin |
| `multiproof::well_formed_merged` | multiproof.rs:309 | translates | elaborates | not run | new gate | not present at the pin |
| `multiproof::verify_counting_merged` | multiproof.rs:366 | translates | elaborates | not run | new gate | not present at the pin |
| `multiproof::merged_level` | multiproof.rs:400 | translates | elaborates | not run | new gate | not present at the pin |
| `program::pool_route::CLOSE_CHECKPOINT_TAG` | pool_route.rs:6 | translates | elaborates | not run | new gate | not present at the pin |
| `program::pool_route::is_close_checkpoint` | pool_route.rs:9 | translates | elaborates | not run | (b) PIN2-new. Same PCXQ_E002 emission; tagged OFF_EMISSION_WRAPPING (`data; NOT SETTLED | (c) no | yes |
| `program::pool_route::admitted` | pool_route.rs:16 | translates | elaborates | not run | (b) PIN2-changed. PCXQ_E002 emission (Charon daad69be + Aeneas 959659a6, p; NOT SETTLED | (c) no (it extracts) | yes |
| `program::r1_pool_adapter::ASPU_HEADER` | r1_pool_adapter.rs:52 | translates | elaborates | not run | new gate | not present at the pin |
| `program::r1_pool_adapter::ASPU_AUTHORITY` | r1_pool_adapter.rs:53 | translates | elaborates | not run | new gate | not present at the pin |
| `program::r1_pool_adapter::CHECKPOINT_TAIL_BYTES` | r1_pool_adapter.rs:54 | translates | elaborates | not run | new gate | not present at the pin |
| `program::r1_pool_adapter::ASRU_MAGIC` | r1_pool_adapter.rs:55 | translates | elaborates | not run | new gate | not present at the pin |
| `program::r1_pool_adapter::ASRU_BODY_BYTES` | r1_pool_adapter.rs:56 | translates | elaborates | not run | new gate | not present at the pin |
| `program::r1_pool_adapter::PROFILE_BINDING` | r1_pool_adapter.rs:68 | translates | elaborates | not run | new gate | not present at the pin |
| `program::r1_pool_adapter::RELEASE_BINDING` | r1_pool_adapter.rs:73 | translates | elaborates | not run | new gate | not present at the pin |
| `program::r1_pool_adapter::AUDIT_POOL_PROGRAM` | r1_pool_adapter.rs:80 | NO: Internal error, please file an issue |  | not run | new gate | not present at the pin |
| `program::r1_pool_adapter::AUDIT_REGISTRY_PROGRAM` | r1_pool_adapter.rs:84 | NO: Internal error, please file an issue |  | not run | new gate | not present at the pin |
| `program::r1_pool_adapter::pool_program_id` | r1_pool_adapter.rs:89 | translates | elaborates | not run | (b) HAND MODEL / TRUST: op45. `deployment_ids::deployment_id` is CE18 (Aen | (c) n/a (HM-A by owner decision) | yes |
| `program::r1_pool_adapter::registry_program_id` | r1_pool_adapter.rs:94 | translates | elaborates | not run | (b) Same mechanism as pool_program_id (deployment_ids::deployment_id, CE18 | (c) n/a (HM-A) | yes |
| `program::r1_pool_adapter::AUDIT_POLICY_BINDING` | r1_pool_adapter.rs:97 | translates | elaborates | not run | new gate | not present at the pin |
| `program::r1_pool_adapter::PAIR_FOREST_MASTER_SEED` | r1_pool_adapter.rs:99 | translates | elaborates | not run | new gate | not present at the pin |
| `program::r1_pool_adapter::PAIR_FOREST_LANE_SEED` | r1_pool_adapter.rs:100 | translates | elaborates | not run | new gate | not present at the pin |
| `program::r1_pool_adapter::PAIR_FOREST_CHECKPOINT_SEED` | r1_pool_adapter.rs:101 | translates | elaborates | not run | new gate | not present at the pin |
| `program::r1_pool_adapter::VERIFIER_REGISTRY_SEED` | r1_pool_adapter.rs:102 | translates | elaborates | not run | new gate | not present at the pin |
| `program::r1_pool_adapter::VERIFIER_ENTRY_SEED` | r1_pool_adapter.rs:103 | translates | elaborates | not run | new gate | not present at the pin |
| `program::r1_pool_adapter::VERIFIER_REGISTRY_V2_SEED` | r1_pool_adapter.rs:104 | translates | elaborates | not run | new gate | not present at the pin |
| `program::r1_pool_adapter::VERIFIER_ENTRY_V2_SEED` | r1_pool_adapter.rs:105 | translates | elaborates | not run | new gate | not present at the pin |
| `program::r1_pool_adapter::{program::r1_pool_adapter::LifecycleKind}::from_byte` | r1_pool_adapter.rs:115 | translates | elaborates | not run | (b) OFF THE ADMITTED SURFACE. It is compiled, and `process` still routes t | (c) n/a (unreachable under `admitted`) | yes |
| `program::r1_pool_adapter::{program::r1_pool_adapter::LifecycleKind}::magic` | r1_pool_adapter.rs:123 | translates | elaborates | not run | (b) OFF THE ADMITTED SURFACE. It is compiled, and `process` still routes t | (c) n/a (unreachable under `admitted`) | yes |
| `program::r1_pool_adapter::{program::r1_pool_adapter::LifecycleKind}::body_len` | r1_pool_adapter.rs:130 | translates | elaborates | not run | (b) OFF THE ADMITTED SURFACE. It is compiled, and `process` still routes t | (c) n/a (unreachable under `admitted`) | yes |
| `program::r1_pool_adapter::{program::r1_pool_adapter::LifecycleKind}::writable_prefix_len` | r1_pool_adapter.rs:140 | translates | elaborates | not run | (b) OFF THE ADMITTED SURFACE. It is compiled, and `process` still routes t | (c) n/a (unreachable under `admitted`) | yes |
| `program::r1_pool_adapter::readonly_meta_ok` | r1_pool_adapter.rs:170 | translates | elaborates | not run | (b) EXTRACTED: AdapterRwModel | (c) no (the frozen function extracts; what r | yes |
| `program::r1_pool_adapter::readonly_buffer_meta_ok` | r1_pool_adapter.rs:191 | translates | elaborates | not run | (b) EXTRACTED: AdapterRwModel; SETTLED | (c) no | yes |
| `program::r1_pool_adapter::decode_public_statement_box` | r1_pool_adapter.rs:237 | translates | elaborates | not run | (b) EXTRACTED: op47, PROVED_CONDITIONAL in PCVV slot47 (fresh E008, T0). C; NOT SETTLED | (c) no for the wrapper; yes for the raw deco | yes |
| `program::r1_pool_adapter::lifecycle_accounts` | r1_pool_adapter.rs:247 | NO: Inconsistent projection: |  | NO: Instantiating the type parameters of a function with types containing mutable borrows is currently not allowed (@SliceIndexShared<'_, solana | (b) OFF THE ADMITTED SURFACE. It is compiled, and `process` still routes t | (c) n/a (unreachable under `admitted`) | yes |
| `program::r1_pool_adapter::validate_lifecycle_header` | r1_pool_adapter.rs:274 | translates | elaborates | not run | (b) OFF THE ADMITTED SURFACE. It is compiled, and `process` still routes t | (c) n/a (unreachable under `admitted`) | yes |
| `program::r1_pool_adapter::validate_lifecycle_final_body` | r1_pool_adapter.rs:309 | translates | elaborates | not run | (b) OFF THE ADMITTED SURFACE. It is compiled, and `process` still routes t | (c) n/a (unreachable under `admitted`) | yes |
| `program::r1_pool_adapter::lifecycle_init` | r1_pool_adapter.rs:343 | translates | error: expected a product type, got core.ops.control_flow.ControlFlow (core.result.Result AspisXPNewLib.Never solana_program_error.ProgramError) (solana_acco | not run | (b) OFF THE ADMITTED SURFACE. It is compiled, and `process` still routes t | (c) n/a (unreachable under `admitted`) | yes |
| `program::r1_pool_adapter::lifecycle_write` | r1_pool_adapter.rs:368 | translates | error: expected a product type, got core.ops.control_flow.ControlFlow (core.result.Result AspisXPNewLib.Never solana_program_error.ProgramError) (solana_acco | not run | (b) OFF THE ADMITTED SURFACE. It is compiled, and `process` still routes t | (c) n/a (unreachable under `admitted`) | yes |
| `program::r1_pool_adapter::lifecycle_finalize` | r1_pool_adapter.rs:405 | translates | error: expected a product type, got core.ops.control_flow.ControlFlow (core.result.Result AspisXPNewLib.Never solana_program_error.ProgramError) (solana_acco | not run | (b) OFF THE ADMITTED SURFACE. It is compiled, and `process` still routes t | (c) n/a (unreachable under `admitted`) | yes |
| `program::r1_pool_adapter::decode_master_box` | r1_pool_adapter.rs:429 | translates | elaborates | not run | (b) EXTRACTED wrapper: op48, PROVED_CONDITIONAL (PCVV slot48; fresh E008) ; NOT SETTLED | (c) yes (raw decoder CE15) | yes |
| `program::r1_pool_adapter::decode_checkpoint_box` | r1_pool_adapter.rs:437 | translates | elaborates | not run | (b) EXTRACTED wrapper: op49, PROVED_CONDITIONAL (PCVV slot49). NKY-RT216 (; NOT SETTLED | (c) yes (raw decoder CE15) | yes |
| `program::r1_pool_adapter::decode_lane_from_pool_release` | r1_pool_adapter.rs:448 | NO: Early returns inside of loops are not supported yet |  | not run | (b) CANNOT-EXTRACT (PCXN_CANNOT_EXTRACT.json CE01): op50, "Early returns i | (c) yes | yes |
| `program::r1_pool_adapter::scan_proof_buffer` | r1_pool_adapter.rs:780 | translates | elaborates | not run | (b) EXTRACTED: op51, PROVED_CONDITIONAL (PCVV slot51, PRVEq_AdapterCallees; NOT SETTLED | (c) no | no |
| `program::r1_pool_adapter::asq8_common` | r1_pool_adapter.rs:814 | translates | elaborates | not run | (b) EXTRACTED: AspisR1AdapterReconstruct.Funs; SETTLED | (c) no | yes |
| `program::r1_pool_adapter::transfer_statement_box` | r1_pool_adapter.rs:833 | translates | elaborates | not run | (b) EXTRACTED: AspisR1AdapterReconstruct.Funs, AspisR1AdapterReconstruct.T | (c) no (the frozen function extracts; what r | yes |
| `program::r1_pool_adapter::withdrawal_statement_box` | r1_pool_adapter.rs:847 | translates | elaborates | not run | (b) EXTRACTED: AspisR1AdapterReconstruct.Funs, AspisR1AdapterReconstruct.T | (c) no (the frozen function extracts; what r | yes |
| `program::r1_pool_adapter::reconstruct_asq8_statement` | r1_pool_adapter.rs:861 | translates | elaborates | not run | (b) EXTRACTED: op52, PROVED_AT_GATE_LEVEL (PCVV slot52; fresh PCWE_E001, O; NOT SETTLED | (c) no | yes |
| `program::r1_pool_adapter::emit_result` | r1_pool_adapter.rs:927 | translates | elaborates | not run | (b) NO EMISSION: op53, BLOCKED_NO_FROZEN_EMISSION. Deployed slot = LIBB_Po | (c) not established (no extraction attempt r | yes |
| `program::r1_pool_adapter::close_checkpoint` | r1_pool_adapter.rs:964 | NO: Inconsistent projection: |  | NO: Instantiating the type parameters of a function with types containing mutable borrows is currently not allowed (@SliceIndexShared<'_, solana | (b) CANNOT-EXTRACT (PIN2_CANNOT_EXTRACT.json): `let [checkpoint, base] = a | (c) yes (or an Aeneas fix for PtrMetadata on | yes |
| `program::r1_pool_adapter::process` | r1_pool_adapter.rs:999 | translates | elaborates | not run | (b) PIN2-changed (new arm 7 to close_checkpoint). PCXQ_E002 emission (T0, ; NOT SETTLED | (c) no | yes |
| `program::r1_pool_adapter::owned::{program::r1_pool_adapter::owned::OwnedAccount}::key` | r1_pool_adapter_owned.rs:19 | translates | elaborates | not run | (b) Accessors inside the stage transcriptions and the AdapterRw ops. No se | (c) no (trivial accessor) | yes |
| `program::r1_pool_adapter::owned::{program::r1_pool_adapter::owned::OwnedAccount}::owner` | r1_pool_adapter_owned.rs:20 | translates | elaborates | not run | (b) Accessors inside the stage transcriptions and the AdapterRw ops. No se | (c) no (trivial accessor) | yes |
| `program::r1_pool_adapter::owned::{program::r1_pool_adapter::owned::OwnedAccount}::data` | r1_pool_adapter_owned.rs:21 | translates | elaborates | not run | (b) EXTRACTED: NMT_stage1_owned `OwnedAccount.data` DEPENDS_ON_LIBRARY_TRU | (c) no | yes |
| `program::r1_pool_adapter::owned::{program::r1_pool_adapter::owned::OwnedAccount}::data_len` | r1_pool_adapter_owned.rs:24 | translates | elaborates | not run | (b) Accessors inside the stage transcriptions and the AdapterRw ops. No se | (c) no (trivial accessor) | yes |
| `program::r1_pool_adapter::owned::snapshot` | r1_pool_adapter_owned.rs:29 | translates | elaborates | not run | (b) Inside the stage1/stage2 transcription windows (TX1:344 / TX2:240). No | (c) yes (with stage1/stage2, CE20/CE21) | yes |
| `program::r1_pool_adapter::owned::require_readonly_buffer` | r1_pool_adapter_owned.rs:45 | translates | elaborates | not run | (b) EXTRACTED: AdapterRwModel EQUALITY_PROVED_JOB. SETTLED. | (c) no | yes |
| `program::r1_pool_adapter::owned::require_readonly_account` | r1_pool_adapter_owned.rs:48 | translates | elaborates | not run | (b) EXTRACTED: AdapterRwModel DEPENDS_ON_LIBRARY_TRUST (HM row). Other (no | (c) no | yes |
| `program::r1_pool_adapter::owned::require_verifier_checkpoint` | r1_pool_adapter_owned.rs:51 | translates | elaborates | not run | (b) EXTRACTED: AdapterRwModel CONDITIONAL_ON_BINDING. NOT SETTLED.; NOT SETTLED | (c) no | yes |
| `program::r1_pool_adapter::owned::require_distinct_accounts` | r1_pool_adapter_owned.rs:59 | NO: Returns inside of nested loops are not supported yet |  | not run | (b) CANNOT-EXTRACT (PCXN_CANNOT_EXTRACT.json CE14): nested `while` with `r; NOT SETTLED | (c) yes | yes |
| `program::r1_pool_adapter::owned::authenticate_invariant_release_registry` | r1_pool_adapter_owned.rs:81 | translates | error: Type mismatch core.array.equality.PartialEqArray.ne has type core.cmp.PartialEq ?m.928 ?m.929 → Std.Array ?m.928 ?m.930 → Std.Array ?m.929 ?m.930 → Re | not run | (b) EXTRACTED gate (AdapterRwModel) OPEN. Its decoder callees are covered ; NOT SETTLED | (c) no for the body; see the decoders | yes |
| `program::r1_pool_adapter::owned::authenticate_asq8_accounts` | r1_pool_adapter_owned.rs:230 | NO: Inconsistent projection: |  | not run | (b) EXTRACTED: AdapterRwModel `authenticate_asq8_accounts` CONDITIONAL_ON_; NOT SETTLED | (c) yes (through CE14 callee) | yes |
| `program::r1_pool_adapter::owned::validate_asq8` | r1_pool_adapter_owned.rs:338 | translates | elaborates | not run | (b) EXTRACTED: AdapterRwModel `validate_asq8` CONDITIONAL_ON_BINDING; PCVV; NOT SETTLED | (c) yes (through CE14 callee) | yes |
| `program::r1_pool_adapter::owned::stage2_owned` | r1_pool_adapter_owned.rs:417 | axiom (opaque or body rejected) |  | not run | (b) EXTRACTED: AdapterRwModel `stage2_owned` CONDITIONAL_ON_BINDING; PCVV_; NOT SETTLED | (c) yes (through CE14 callee) | no |
| `program::r1_pool_adapter::owned::stage1` | r1_pool_adapter_owned.rs:474 | translates | elaborates | not run | (b) HAND MODEL: ReviewedTranscription-TX1:344 (ruling (bn)), now OPEN_TRAN | (c) yes | no |
| `program::r1_pool_adapter::owned::stage2` | r1_pool_adapter_owned.rs:501 | translates | error: Unknown identifier `core.slice.index.SliceIndexRangeFullSlice` | NO: Instantiating the type parameters of a function with types containing mutable borrows is currently not allowed (@SliceIndexShared<'_, solana | (b) HAND MODEL: ReviewedTranscription-TX2:240 (ruling (bn)), OPEN_TRANSCRI | (c) yes | no |
| `r1_semantic::claims` | r1_semantic.rs:42 | NO: Joining region abstractions containing shared loans whose shared value contains borrows is not supported yet |  | not run | (b) CANNOT-EXTRACT (PCXN_CANNOT_EXTRACT.json CE12): Aeneas CFailure on the; NOT SETTLED | (c) yes | yes |
| `r1_semantic::public_transcript` | r1_semantic.rs:63 | translates | elaborates | not run | (b) EXTRACTED at PIN2: PIN2_NEWGATE_r1_semantic (PCXU_E003, Charon 454586e; NOT SETTLED | (c) no | yes |
| `r1_semantic::semantic_boundary` | r1_semantic.rs:91 | translates | elaborates | not run | (b) CANNOT-EXTRACT (PCXN_CANNOT_EXTRACT.json CE11): same Iterator trait-ty; NOT SETTLED | (c) yes | no |
| `r1_semantic::semantic_value` | r1_semantic.rs:145 | translates | elaborates | not run | (b) EXTRACTED: AspisR1SemanticCallExtraction keys OPEN. 14k: "emitted but  | (c) no (library models missing; not a constr | no |
| `r1_semantic::semantic_round` | r1_semantic.rs:153 | translates | elaborates | not run | (b) No key. It is called only from semantic_rounds (CE13), and the record  | (c) not established | yes |
| `r1_semantic::semantic_rounds` | r1_semantic.rs:190 | translates | elaborates | not run | (b) CANNOT-EXTRACT (PCXN_CANNOT_EXTRACT.json CE13): same crash. No key. NO; NOT SETTLED | (c) yes | yes |
| `r1_wire::DOMAIN` | r1_wire.rs:12 | translates | elaborates | not run | new gate | not present at the pin |
| `r1_wire::LANES` | r1_wire.rs:13 | translates | elaborates | not run | new gate | not present at the pin |
| `r1_wire::POINTS` | r1_wire.rs:14 | translates | elaborates | not run | new gate | not present at the pin |
| `r1_wire::CLAIMS` | r1_wire.rs:15 | translates | elaborates | not run | new gate | not present at the pin |
| `r1_wire::row_shape` | r1_wire.rs:39 | translates | elaborates | not run | (b) EXTRACTED: AspisR1PrefixAggregateParser.Funs, AspisR1RecordParser.Funs; SETTLED | (c) no | yes |
| `r1_wire::validate_record_fields` | r1_wire.rs:51 | translates | elaborates | not run | (b) EXTRACTED: AspisR1PrefixAggregateParser.Funs, AspisR1RecordParser.Funs; SETTLED | (c) no | no |
| `r1_wire::validate_record_fields_pinned` | r1_wire.rs:59 | translates | elaborates | not run | new gate | not present at the pin |
| `r1_wire::validate_record_fields_lean` | r1_wire.rs:74 | translates | elaborates | not run | new gate | not present at the pin |
| `r1_wire::parse_record` | r1_wire.rs:136 | translates | elaborates | not run | (b) EXTRACTED: AspisR1PrefixAggregateParser.Funs, AspisR1RecordParser.Funs; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `r1_wire::validated_values` | r1_wire.rs:191 | translates | elaborates | not run | new gate | not present at the pin |
| `r1_wire::validated_limb` | r1_wire.rs:202 | translates | elaborates | not run | new gate | not present at the pin |
| `r1_wire::{r1_wire::ValidatedRecord<'a>}::row` | r1_wire.rs:216 | translates | elaborates | not run | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `r1_wire::{r1_wire::ValidatedRecord<'a>}::framed` | r1_wire.rs:220 | translates | elaborates | not run | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `r1_wire::{r1_wire::ValidatedRecord<'a>}::payload` | r1_wire.rs:224 | translates | elaborates | not run | (b) EXTRACTED: AspisR1DecodeKFullV10.Funs; SETTLED | (c) no | yes |
| `r1_wire::{r1_wire::ValidatedRecord<'a>}::decode_k` | r1_wire.rs:232 | translates | elaborates | not run | (b) CANNOT-EXTRACT (PCXN_CANNOT_EXTRACT.json CE04): "Joining region abstra | (c) yes | no |
| `r1_wire::{r1_wire::SemanticTranscript<H>}::new` | r1_wire.rs:280 | translates | elaborates | not run | (b) EXTRACTED: AspisR1PublicPreparation.Types; SETTLED | (c) no | yes |
| `r1_wire::{r1_wire::SemanticTranscript<H>}::state` | r1_wire.rs:288 | translates | elaborates | not run | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `r1_wire::{r1_wire::SemanticTranscript<H>}::sample_block_validated` | r1_wire.rs:295 | translates | elaborates | not run | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `r1_wire::{r1_wire::SemanticTranscript<H>}::semantic_validated` | r1_wire.rs:321 | translates | elaborates | not run | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `r1_wire::{r1_wire::SemanticTranscript<H>}::circle_validated` | r1_wire.rs:334 | translates | elaborates | not run | (b) OPEN GAP: no key in the 1,707-key universe and no constant of this nam | (c) not established | yes |
| `r1_wire::parse_record_at` | r1_wire.rs:379 | translates | elaborates | not run | (b) EXTRACTED: AspisR1PrefixAggregateParser.Funs; SETTLED | (c) no | yes |
| `r1_wire::{r1_wire::Prefix<'a>}::parse` | r1_wire.rs:393 | translates | elaborates | not run | (b) EXTRACTED: AspisR1PrefixAggregateParser.Funs; SETTLED | (c) no | yes |
| `r1_wire::{r1_wire::Prefix<'a>}::record` | r1_wire.rs:439 | translates | elaborates | not run | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `r1_wire::{r1_wire::Prefix<'a>}::payload` | r1_wire.rs:445 | translates | elaborates | not run | (b) EXTRACTED: AspisR1DecodeKFullV10.Funs; SETTLED | (c) no | yes |
| `r1_wire::{r1_wire::Prefix<'a>}::validated_record` | r1_wire.rs:449 | translates | elaborates | not run | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `r1_wire::begin` | r1_wire.rs:491 | translates | elaborates | not run | (b) EXTRACTED: AspisR1PublicPreparation(+PIN2) constants and PIN2_NEWGATE_ | (c) no | yes |
| `sampler::qm31_div_pass` | sampler.rs:11 | translates | elaborates | not run | (b) EXTRACTED: AspisR1Post25Sampler.Funs, AspisR1Qm31SamplerIndex.Funs; SETTLED | (c) yes (the current model is a rewritten cr | yes |
| `sampler::qm31_digits` | sampler.rs:24 | translates | elaborates | not run | (b) EXTRACTED: AspisR1Qm31SamplerIndex.Funs; SETTLED | (c) no | yes |
| `sampler::qm31_sample` | sampler.rs:45 | translates | elaborates | not run | (b) EXTRACTED: AspisR1Qm31SamplerIndex `qm31_sample` EQUALITY_PROVED_JOB,  | (c) no | yes |
| `sampler::low_base_p_digits` | sampler.rs:56 | translates | error: expected a product type, got { l // l.length = ↑8#usize } | not run | (b) REWRITTEN-CRATE EMISSION: AspisR1Post25Sampler.Funs (crate `r1_post25_ | (c) yes | yes |
| `sampler::decode8` | sampler.rs:75 | translates | elaborates | not run | (b) EXTRACTED: AspisR1Post25Sampler.Funs; SETTLED | (c) yes (the current model is a rewritten cr | yes |
| `sampler::add_small_base_p` | sampler.rs:91 | translates | error: Unknown identifier `MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter` | not run | (b) REWRITTEN-CRATE EMISSION: AspisR1Post25SamplerIndexedAddSmallCandidate | (c) no by construct (the frozen form emits c | yes |
| `sampler::ordinary_sample` | sampler.rs:102 | translates | elaborates | not run | (b) REWRITTEN-CRATE EMISSION: AspisR1Post25Sampler `ordinary_sample` OPEN ; NOT SETTLED | (c) yes (through low_base_p_digits) | yes |
| `sampler::gamma_sample` | sampler.rs:111 | translates | elaborates | not run | (b) REWRITTEN-CRATE EMISSION: GammaCallerExplicitHelpers (`aspis_r1_stage2; NOT SETTLED | (c) yes (through low_base_p_digits; the gamm | yes |
| `sampler::circle_sample` | sampler.rs:121 | translates | elaborates | not run | (b) REWRITTEN-CRATE EMISSION: RPz7_AspisR1CircleSampleWrapper_Funs (`r1_ci; NOT SETTLED | (c) not established (no frozen extraction at | yes |
| `trace::value` | trace.rs:6 | translates | elaborates | not run | (b) EXTRACTED: FIo_Native `trace.value` EQUALITY_PROVED (PRVEq.RPz7_FIo_Na | (c) no | yes |
| `transcript::{transcript::Transcript<H>}::new` | transcript.rs:7 | translates | elaborates | not run | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `transcript::{transcript::Transcript<H>}::resume` | transcript.rs:18 | translates | elaborates | not run | new gate | not present at the pin |
| `transcript::{transcript::Transcript<H>}::absorb` | transcript.rs:19 | translates | elaborates | not run | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `transcript::{transcript::Transcript<H>}::block` | transcript.rs:22 | translates | elaborates | not run | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `transcript::{transcript::Transcript<H>}::scalar` | transcript.rs:28 | translates | elaborates | not run | (b) No key in the 1,707 universe and no constant of this name in the cone. | (c) not established | yes |
| `transcript::{transcript::Transcript<H>}::scalar_k` | transcript.rs:36 | translates | elaborates | not run | (b) No key in the 1,707 universe and no constant of this name in the cone. | (c) not established | yes |
| `transcript::{transcript::Transcript<H>}::queries` | transcript.rs:40 | translates | elaborates | not run | (b) EXTRACTED: AspisR1PublicPreparation `transcript.Transcript.queries` co | (c) no | yes |
| `transport::TAU` | transport.rs:4 | translates | elaborates | not run | new gate | not present at the pin |
| `transport::{transport::Variant}::tag` | transport.rs:6 | translates | elaborates | not run | (b) EXTRACTED: NJS_Extract.Funs, Op3I_Source; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `transport::{transport::Variant}::folds` | transport.rs:8 | translates | elaborates | not run | (b) EXTRACTED: FinishCandidateExplicitOps; SETTLED | (c) no | yes |
| `program::r1_pool_adapter::v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS` | v7_pair_empty_roots.rs:14 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::SEMANTIC_BYTES` | verifier.rs:8 | translates | elaborates | not run | new gate | not present at the pin |
| `verifier::checkpoint_size` | verifier.rs:32 | axiom (opaque or body rejected) |  | not run | (b) OPEN GAP: no key in the 1,707-key universe and no constant of this nam | (c) not established | yes |
| `verifier::echeck` | verifier.rs:40 | translates | elaborates | not run | (b) HAND MODEL: ReviewedTranscription NJZ-RT189 (REACHED, NJZ_native.patch | (c) not established (no fresh extraction rec | yes |
| `verifier::prepared_claim` | verifier.rs:53 | NO: Returns inside of nested loops are not supported yet |  | not run | (b) CANNOT-EXTRACT (PCXN_CANNOT_EXTRACT.json CE03): "Returns inside of nes; NOT SETTLED | (c) yes | no |
| `verifier::{verifier::Prepared}::new` | verifier.rs:85 | NO: Unreachable |  | not run | (b) CANNOT-EXTRACT (PCXN_CANNOT_EXTRACT.json CE03): "Unreachable" at verif; NOT SETTLED | (c) yes | yes |
| `verifier::batch_prefix_products` | verifier.rs:151 | translates | elaborates | not run | (b) EXTRACTED: NFN_ExtractedGeometry, Port4C_NativePrefix; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `verifier::{verifier::QueryGeometry}::for_range` | verifier.rs:161 | NO: Could not match the contexts |  | not run | (b) EXTRACTED: NFN_ExtractedGeometry, Port3_NativeGeometryBody, Stage2Cont; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `verifier::{verifier::QueryGeometry}::for_query` | verifier.rs:192 | translates | elaborates | not run | (b) OPEN GAP: no key in the 1,707-key universe and no constant of this nam | (c) not established | yes |
| `verifier::polynomial` | verifier.rs:305 | translates | elaborates | not run | (b) HAND MODEL: ReviewedTranscription-polynomial (TX2:119; NHE_Polynomial  | (c) not established (`(0..7).rev().fold`: Re | yes |
| `verifier::finish_relation_round` | verifier.rs:306 | translates | elaborates | not run | (b) EXTRACTED: FinishCandidateExplicitOps; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `verifier::PROOF_BYTES` | verifier.rs:532 | axiom (opaque or body rejected) |  | not run | new gate | not present at the pin |
| `weights::QUARTER` | weights.rs:5 | translates | elaborates | not run | new gate | not present at the pin |
| `weights::PERM` | weights.rs:6 | translates | elaborates | not run | new gate | not present at the pin |
| `weights::powers` | weights.rs:11 | translates | elaborates | not run | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `weights::double` | weights.rs:24 | translates | elaborates | not run | (b) OPEN GAP: no key in the 1,707-key universe and no constant of this nam | (c) not established | yes |
| `weights::field` | weights.rs:25 | translates | elaborates | not run | (b) EXTRACTED: WeightsFieldExplicitDecoder; SETTLED | (c) no | yes |
| `weights::S2_INACTIVE_GROUPS` | weights.rs:29 | translates | elaborates | not run | new gate | not present at the pin |
| `weights::S2_INACTIVE_MASKS` | weights.rs:30 | translates | elaborates | not run | new gate | not present at the pin |
| `weights::factored_s2_libra_weights` | weights.rs:108 | translates | elaborates | not run | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `weights::{weights::Weights}::box_from_parts` | weights.rs:202 | translates | elaborates | not run | (b) OPEN GAP: no key in the 1,707-key universe and no constant of this nam | (c) not established | yes |
| `weights::{weights::Weights}::new` | weights.rs:210 | translates | elaborates | not run | (b) OPEN GAP: no key in the 1,707-key universe and no constant of this nam | (c) not established | yes |
| `weights::{weights::Weights}::scalar_factor` | weights.rs:237 | translates | elaborates | not run | (b) EXTRACTED: RPz7_FIo_NativeTypes; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `weights::{weights::Weights}::row_product` | weights.rs:374 | translates | elaborates | not run | new gate | not present at the pin |
| `weights::{weights::Weights}::product_rows::KINDS` | weights.rs:381 | translates | elaborates | not run | new gate | not present at the pin |
| `weights::{weights::Weights}::product_rows` | weights.rs:382 | translates | elaborates | not run | new gate | not present at the pin |
| `weights::{weights::Weights}::inactive_tensor` | weights.rs:392 | translates | elaborates | not run | new gate | not present at the pin |
| `weights::{weights::Weights}::mle_at` | weights.rs:401 | translates | elaborates | not run | new gate | not present at the pin |
| `weights::inactive_groups` | weights.rs:416 | translates | elaborates | not run | new gate | not present at the pin |
| `weights::kappa_sum` | weights.rs:421 | translates | elaborates | not run | new gate | not present at the pin |
| `weights::digit_dot` | weights.rs:426 | translates | elaborates | not run | new gate | not present at the pin |
| `weights::perm_dot` | weights.rs:431 | translates | elaborates | not run | new gate | not present at the pin |
| `weights::libra_at` | weights.rs:436 | translates | elaborates | not run | new gate | not present at the pin |


## 3. Patch 0 (restoration): gate results

Three versions were gated. All are restorations of pinned text; none is a
translatability rewrite. The third is the patch.

First version (sha256
22adb5a3246292b805caa07a70c8503a8a9c915b36c3aa6e7c2cdf1da632f7eb, gate name
`tp1-p0`, run by the shared script `fv_sampler_gate.sh`). Failed. Recorded
transfer 1,290,240 and recorded withdrawal 1,296,723 compute units against
1,280,964 and 1,287,485 for the base ELF: 9,276 and 9,238 more. Cause: the
patch switched `semantic_value` on `feature = "future-lazy-horner"`, which
the verifier crate did not have, so the deployed build compiled the pinned
`semantic_value` (multiply, then add) in place of the single-reduction form.
The integration tests, the replay conditions, the redirect attempts and the
mutant verdict comparison had passed; the gate was stopped by hand at the
worst-case tool build once the cause was known, and it has no done-file.

Second version (sha256
afce19eda5b4e80564ba3cd52ebd94da178f6d0fc127dd8408b74bc3a87c67ff, gate name
`tp1-p0b`, run by `fv_tp1_gate.sh`). It added the verifier crate's
`future-lazy-horner` feature and still restored all 13 functions. Every gate
passed except compute: recorded transfer 1,282,809 and withdrawal 1,289,330,
1,845 more than the base on both, and 1,845 more in all eighteen worst-case
runs. ELF sha256
58a6e307c8cf497cbdf92e6681c87f24f2ea6c8a4e0ebdac672caec37a23a6bb, 972,088
bytes. Function-by-function comparison of the unstripped ELFs
(`fv_tp1_symcmp.sh`): `canonical_scan_pinned` (3,248 bytes) gone and
`canonical_scan` from a 24-byte thunk to the 3,248-byte body, which is the
thunk removal; `Prepared::new` from 30,312 to 30,352 bytes; no other function
changes size.

Where the 1,845 units are. `Prepared::new` has the same text in both trees;
what differs is `prepared_claim`, which the compiler inlines into it. The
base tree has the experiment's form (`if cfg!(feature="future-claim-rows")
{ … } else { the pinned loop }`), the second version has the pinned function.
Under the deployed features both are the same loop over 6 points and 29
lanes, but the compiler's register use inside the loop differs (more reloads
from the stack without the dead branch). This was then separated by a build
(run `b2` of `fv_tp1_bisect.sh`, one scratch tree rebuilt per variant in one
host scope, the control row reproducing the gated ELF 58a6e307c8cf497cbdf92e6681c87f24f2ea6c8a4e0ebdac672caec37a23a6bb): the
restored tree with `prepared_claim` left as the base tree has it costs
1,280,961 on the recorded transfer and 1,287,482 on the withdrawal, 3 units
less than the base. So all of the 1,845 units are `prepared_claim`, and the
rest of the restoration is the thunk removal.

Third version (sha256
8a8f3f1e66964aab221d051043d2a116385b92e803af260be4a51b0963ab2779, gate name
`tp1-p0d`, run by `fv_tp1_gate2.sh`): the second version without
`prepared_claim`, which is a rewrite candidate and is replaced by the batch.
One scope (`TP-G-tp1-p0d`): exit 0, wall 11:00, peak resident set 1,789,776
kB, scope memory peak 1,877,585,920 bytes, no memory event. Gate status OK.
(A first run of this gate, `tp1-p0c`, was stopped by hand: my gate script
failed the gate whenever a program-crate test failed, and 25 fail in the base
tree itself under the deployed features.)

| Gate | Result |
|---|---|
| unit tests of the verifier crate, deployed features | 53 passed, 0 failed |
| client configuration (`r1p-check`), unit tests named prover or sim | 15 passed, 0 failed |
| unit tests of the program crate, deployed features, both trees | 89 tests, 25 failing in the changed tree and the same 25 in the base tree (R1's two-transaction checkpoint tests, which the one-transaction configuration rejects at stage 1); outcome lists identical |
| unit tests of the program crate, R1's features (`pool-adapter,private-leaf-salts`), both trees | 89 tests, 0 failing in both; outcome lists identical |
| integration tests (nine test files, deployed features) | pass |
| SBF build, deployed features | ELF sha256 74b28d04f8de3ac4ef9565fb9924a252074bbf02b1c900567aa28b877631db3a, 972,048 bytes (base ELF 7540abe6c5f07827011b11d3313fe5594816a32fa05963195ee4a1f5cf7856b5, 972,072 bytes) |
| recorded transfer replayed | 1,280,961 (base 1,280,964): 3 less; all replay conditions hold |
| recorded withdrawal replayed | 1,287,482 (base 1,287,485): 3 less; all replay conditions hold |
| redirect attempts | exit 0 |
| mutant campaign, both trees | verdict files identical, sha256 e3659a53d3b4e308711668d82715cd981e8d3bdc7ba859c9ff3bdaa1e3c9e2b9 |
| worst-case tool built in the changed tree, six scenarios, three marker variants each | prover output identical to the unchanged tree in all six; changed ELF minus base ELF is -3 in all eighteen runs; no errors |
| function comparison of the unstripped ELFs | `.text` 939,576 to 939,552 bytes; `canonical_scan_pinned` (3,248 bytes) gone, `canonical_scan` from the 24-byte thunk to the 3,248-byte body; no other function changes size |

So patch 0 changes compute by the thunk removal alone: 3 units less on every
measured case.

Build without the Aspis features (`pool-adapter,private-leaf-salts`, the
recipe of `fv_build_adapter_src.sh`), compared with
`devnet/verifier-pin2.so` (sha256
2284239edf238730aa0def62ec06176c364f6cb35cef1934ca18b0df0fbd6278, 1,567,992
bytes), script `fv_tp1_r1cmp.sh`. These builds were made on the second
version of the patch.

| Tree | Result |
|---|---|
| `src-tp1-pin`: `git archive` of c7593d23fdc (control for the recipe) | identical to `devnet/verifier-pin2.so` |
| `src-tp1-p0s`: base tree + patch 0 (second version) + the pinned `sampler.rs` | differs: 1,568,048 bytes, sha256 ed9ed197188227e11cfa3bec995e67b93a1cc24a85d9f8e21f5a1c5666b5842a |
| `src-tp1-p0sc`: the same with the pinned aspis-core `src/field.rs` as well | differs: 1,568,048 bytes, sha256 7bc1885aee0e84c810a5272d102878b3b11a6d21991575ee20c2ecdf3a3ea01c |

So the sampler rewrite is not the only cause, and the R1-feature build of the
restored tree is not byte-equal to the PIN2 verifier. Against the control,
both trees have the same 283 function symbols and two functions of different
size: `verifier::finish_relation` (5,664 to 5,696 bytes) and
`verifier::finish_relation_round` (2,816 to 2,840 bytes). Both have text
identical to the pin (function-text comparison of the second version against
the pin: 716 identical, 13 identical under an added `#[cfg]`, two changed,
which are the sampler functions).
Putting the pinned aspis-core `field.rs` back does not change the two sizes
(the pinned `digest.rs` cannot be put back: the head's verifier calls
`Digest32::digest_into`, which it lacks). The cause was not separated by a
build. `finish_relation_round` is called from four functions of `fused.rs`
(eight call sites) that do not exist at the pin, where its only caller is
`finish_relation`; that is the likeliest reason the compiler treats it
differently. With the third version the R1-feature build has the base
tree's `prepared_claim` in place of the pinned one; that build was not made.

## 4. The batch (translatability rewrites)

`patches/tp1-b1-translatability.patch`, sha256
a353f3d796dd4bcf7abf1e571ec95fb4151eab70bab371190e70ddb7bcae522b, made with
`diff -ruN` against the base tree with patch 0 applied; built by
`tools/TP_rewrite_p1.py`, `TP_rewrite_p2.py` and `TP_rewrite_p3.py` with
their default arguments, in that order. The two patches applied in order to
`src-base2` give the final tree; that was checked on a local copy, and the
eleven changed files of the host tree the gate ran on (`src-tp1-b1`) have the
same hashes as that copy: `Cargo.toml` and
`src/{candidate,fast_pairing,fused,r1_semantic,r1_wire,verifier}.rs` of the
verifier crate, `Cargo.toml` and `src/{lib,r1_pool_adapter,r1_pool_adapter_owned}.rs`
of the program crate. Nothing else under `crates/` and `programs/` differs
from `src-base2`; outside them the only difference is the worst-case tool's
source, which the gate copies into the tree's `tools/r1-cost-probe/src/bin/`
as the shared gate does (checked with `diff -rq`).

The batch went through several earlier trees; each was stopped by a gate or
by the tools, and what each taught is in 4.1 and 4.2.

### 4.1 What is rewritten

"Called by the client's publish step" means reachable from
`fused::to_summed_format` (the re-pack that publishes the summed format, behind
`feature = "prover"`), which calls `stage_d_vectors`, which calls
`parse_shape`, `canonical_scan`, `candidate::prepare`, `for_range` and
`fold_sums`. Checked by reading the call chain and by a text search of the
callers; `prover.rs`, `RealR1_client.rs` and `crates/aspis-prover` do not
name any rewritten function. The program crate is not a dependency of the
client tools (`tools/r1-cost-probe/Cargo.toml`). The gate's check on this is
the worst-case tool built in the changed tree: the pinned proof and the
re-packed proof it makes have the same hashes as those made in the unchanged
tree, in all six scenarios.

| Function | R1 row status (column (c)) | Change | Called by the client's publish step? | Operators, effect order, error precedence |
|---|---|---|---|---|
| `verifier::prepared_claim` (R1) | CANNOT-EXTRACT CE03 ("Returns inside of nested loops"); model is a reviewed transcription, open; (c) yes | R1's claim-fission text (`lean-candidates/s1-claim-fission-sum-proved-candidate-20261020/claim-fission.patch`): the 29-lane dot of one point in `prepared_claim_dot`, the weighted sum in `prepared_claim_sum`, no inlining attributes; under `#[cfg(not(feature="future-claim-rows"))]`, the claim-rows variant kept as a second definition under `#[cfg(feature="future-claim-rows")]` | yes | no operator changed; the same `trace::value(14, …)` calls in the same order; the first failing `push` still returns `Parse` |
| `verifier::Prepared::new` (R1) | CANNOT-EXTRACT CE03 ("Unreachable"); no key; (c) yes | the second folding challenge in a helper `second_alpha(&mut t, v)`, `#[inline(never)]` (row 30 over folded root and second round message when there are two folds, zero and no row otherwise); `row` by its own `if` | yes | transcript rows in the same order (27, 28, 29, 30 if two folds, the query row, the row after it); no operator changed |
| `verifier::QueryGeometry::for_range` (R1) | extracted per the table but not settled (non-frozen, detector-blind, five hand-adapted keys); rewrite candidate by the lead's ruling; in these runs neither tool pair translates it ("Could not match the contexts") | the backward pass of the batch inversion in a helper `batch_suffix_inverses` beside the pinned `batch_prefix_products`, as a counting loop (`let mut i = n; while i > 0 { i -= 1; … }`) in place of the reversed range; the grouping of the inverses by five in a helper `group_inverses` (counting loop) in place of `map`, `from_fn` and `collect`; the zero test of the five values as five comparisons joined by `||` in place of `iter().any(…)` | yes | two new operators, both on loop counters that cannot wrap: `i -= 1` guarded by `i > 0`, and `i += 1` below the count; the two multiplications per step in the same order; the same five comparisons in the same order with the same short circuit; `5*i+j` written out for j = 0..4 with the same `*` and `+` |
| `candidate::canonical_scan` (R1, pinned variant) | extracted per the table but not settled (non-frozen; reviewed transcription NKL-RT084, open); rewrite candidate by ruling; second pair: "Continue to outer loops" | per opening a helper `scan_opening` that calls `scan_slot` for slots 0, 1, 2, 3 and then checks the folded values; `scan_slot` calls `scan_slot_base` (the 26-limb loop) and then makes the three extension checks in straight-line code; all three `#[inline(always)]` | yes | the same checks in the same order with the same early exit and the same error (`Parse`); the two-iteration loop over the C2 values is written out; no operator changed |
| `candidate::wide_view` (R1) | extracted per the table, key open, not settled; rewrite candidate by ruling; both pairs: "There should be no bottoms in the value" | the field `query_bytes: &[]` reads a named constant `NO_QUERY_BYTES: &[u8] = &[]` | yes | nothing else changed |
| `r1_semantic::claims` (R1) | CANNOT-EXTRACT CE12; model is R1's rewritten `candidate_claims::claims`; (c) yes | the shape of that rewritten text: zero-filled vector of three rows, boxed slice, conversion to the boxed array, then the three decodes assigned in order; the `unsafe` block is gone. The Rust file of R1's rewrite is no longer on the host and not in this worktree; the text is reconstructed from its emitted Lean and could not be compared byte for byte | yes | record lookup, then allocation, then the decodes at value offsets 0, 29, 58, as pinned; the multiplication `p * 29` of the loop is replaced by its three values |
| `r1_semantic::semantic_boundary` (Aspis variant, `future-lazy-boundary`) | new gate | counting loop over the 28 coefficients; the four reductions written out in place of `map` with a function value | no (the client is built without the feature) | same sums in the same order, `+=` on `u64` as before |
| `r1_semantic::verify_unobserved`, `verify_finish_unobserved` | new gate (Aspis entry) | `verify_observed` and `verify_finish` without the observer parameter and its marks; they call `Prefix::parse`, `public_transcript`, `begin`, `semantic_rounds`, `claims` unchanged. `verify_observed`, `verify_finish` and the two `mark` functions keep their pinned text | no | the same calls in the same order |
| `fast_pairing::KbyKDot::push` | new gate (not at the pin) | `if cfg!(feature = "future-lean-dot")` inside the function becomes two definitions under `#[cfg]` | yes (the checked definition; the client is built without the feature) | the checked definition is the old body without the dead branch |
| `fused::fold_sums`, `summed_final_checks` | new gate | the observer parameter (a function pointer) becomes `Hook`, a zero-sized value unless the new verifier feature `phase-observer` is on | `fold_sums` yes, `summed_final_checks` no | arithmetic untouched; marks become `hook.note(…)` at the same places |
| `fused::verify_summed_format` | new gate | body moved to `verify_summed_format_hooked`; `verify_summed_format(.., obs)` kept for tests, tools and profiling builds; `verify_summed_format_unobserved` is the on-chain entry; `prepare_summed` repeats `candidate::prepare` with the semantic layer entered through `verify_unobserved` | no | the same steps in the same order |
| `fused::coefficients`, `fused::k_of` | new gate | `if cfg!(feature = "future-fold-shared")` becomes two `#[cfg]` blocks; `k_of` writes its four reductions out | yes | same values |
| `fused::base_lanes_tight` | new gate | the conversion of the mutable slice to a mutable array reference by a `match` in place of `map_err` and `?` | yes | same error (`Allocation`) at the same place |
| `r1_pool_adapter_owned::authenticate_asq8_accounts` (R1) | extracted gate, conditional, not settled; (c) yes through its callee; in these runs its own slice pattern fails ("Inconsistent projection") | `let [a, …, g] = accounts else { … }` becomes a length test with the same two errors, then seven indexed borrows; the call of `require_distinct_accounts` on the seven accounts becomes a call of a new `require_distinct_seven`, which makes the same 21 key comparisons in the same order with the same error at the first equal pair | no (program crate) | same error for a short and for a long account list; same error and same first failing pair for duplicate accounts |
| `r1_pool_adapter::decode_lane_from_pool_release` (R1) | CANNOT-EXTRACT CE01 ("Early returns inside of loops"); the reviewed transcription was refused by the owner; (c) yes | the frontier loop moved into a function of its own, `lane_frontier(tree, next_leaf_index)`: a `while` over the 20 levels with a flag, each level's two checks (canonical node; equal to the pinned empty root where the subtree is unoccupied) made by a helper `lane_frontier_node` whose branches all end the function; the error is returned after the loop. The decoder itself has no loop left. The shift amount is written `level as u32` (the R1 Lean library has the shift of a u64 by a u32 only) | no | every failure in the pinned loop is `InvalidAccountData` and the frontier is not used when an error is returned, so the result is the same on every input; the account length is fixed at 768 bytes before the loop, so no level can index out of range; a rejected account now costs the full loop |
| `r1_pool_adapter_owned::stage2_owned` (Aspis variant) | new gate | calls `verify_summed_format_unobserved` unless `cu-profiling` is on | no | same checks before and after the call |

One construct per function, as the tools reported it and as a stand-alone
probe narrowed it (the probes are small crates with stand-in types, run
through the same tool pair; they are not Aspis code and say nothing about
Aspis beyond which shape the tools accept):

- `wide_view`: the struct it returns held the literal `&[]`. At the stage of
  the compiler's output that the tools read, the empty array of that literal
  is a temporary of the function, so the returned struct borrows a local
  whose storage has ended ("There should be no bottoms in the value").
- `Prepared::new`: an `if` one of whose branches unwraps the optional
  folded-root reference read through the shared view, followed by more code.
  The tools cannot merge the two branches ("Unreachable" at the `if`; in the
  probe "Internal error"). The same `if` as the last expression of a helper
  is accepted (probe m01: `second_alpha_v2`, `second_reshaping_owned`
  accepted; `pinned_shape_owned`, `first_reshaping_with_continuation`,
  `conditional_unwrap_with_continuation` rejected). Binding that reference
  out of the `Option` with a pattern (`match v.folded_root { Some(root) => … }`)
  is rejected in every position tried.
- `for_range`: the backward loop is rejected inside the function, as a
  reversed range and as a counting loop ("Could not match the contexts"); in
  a helper that takes slices both forms are accepted (probe m02).
- `canonical_scan`: an early return inside the nested loops ("Continue to
  outer loops are not supported yet"). A loop with `?` followed by further
  `?` lines in the same function is also rejected ("Unexpected return",
  probe m02), which is why the 26-limb loop has a helper of its own.
- `require_distinct_accounts`: with the early return, "Returns inside of
  nested loops"; with a flag in place of the return, "Found a case of
  unsupported nested borrows" (the loop runs over an array of references).
  Probe m02 reproduces both; the written-out comparisons are accepted.
- `decode_lane_from_pool_release`: the tools reject a loop INSIDE this
  function in every body shape tried ("Could not match the contexts"): a
  counting loop with a flag and an `if` that compares with the table of empty
  roots in one branch (rejected at the `if`, emission `TP-A31p`); the two
  checks in a helper and a `match` in the loop that stores the node or sets
  the flag (rejected at the `match`, `TP-A40p`); a loop body with no branch
  at all (rejected at the loop, `TP-A50p`). So the body is not the cause;
  the function's state on entry to the loop is (before it the function has
  taken several sub-slices of the account bytes and returned early on some
  of them). The same loop in a function of its own, which receives the
  sub-slice as a parameter, translates and its Lean elaborates (emission
  `TP-A60p`). This is what happened with
  `for_range`. Three stand-alone probes (m02, m03, m04, the last with an
  error type that owns a string as the SDK's does) accepted every one of
  these loop shapes as a function of its own, which is consistent with that
  reading and is why the probes did not predict the rejections.
- `base_lanes_tight`: translates either way. With `map_err` and `?` on a
  result that holds a mutable reference, the emitted Lean binds a pair from
  `map_err` and from `branch` (a value and a write-back function); no library
  definition has that type, neither R1's nor the second pair's own.

### 4.2 Compute, by rewrite

All figures are compute units of the recorded transfer replayed against the
ELF built with the deployed features (the recorded withdrawal moves by the
same amounts in every row); base ELF 1,280,964. Method: `fv_tp1_bisect.sh`,
one scratch tree (`src-tp1-var`), one SBF target directory, the reference
laid down, one variant's files laid over it, built by
`fv_build_adapter_src.sh`, replayed by `one_tx_replay`; each run is one host
scope. A variant differs from its reference in one function, so the
difference is that rewrite's cost in that context; costs in different
functions add, costs inside one function need not.

Run `b2`, reference = base + patch 0 (second version) + the first batch with
`canonical_scan` in flag form (1,303,558):

| Variant (one thing put back) | Transfer | Reference minus variant |
|---|---|---|
| control: every batch file put back (the restored tree) | 1,282,809 | reproduces gate `tp1-p0b`, same ELF hash |
| `canonical_scan` pinned | 1,282,859 | 20,699: the flag form |
| `claims` pinned | 1,303,438 | 120 |
| `prepared_claim` as in the base tree | 1,301,690 | 1,868: fission text with forced inlining, against the base text |
| `Prepared::new` pinned | 1,303,550 | 8 |
| `for_range` pinned | 1,303,558 | 0 |
| program crate as restored | 1,303,498 | 60 |
| `prepared_claim` `#[inline(never)]` | 1,305,103 | -1,545 (worse) |
| `second_alpha` `#[inline(never)]` | 1,303,438 | 120 (better; adopted) |
| restored tree with the base tree's `prepared_claim` | 1,280,961 | 3 under the base |

Run `b3`, reference R = base + patch 0 (third version) + batch with
`canonical_scan` pinned and the fission helpers `#[inline(always)]`
(1,283,479):

| Variant | Transfer | Variant minus R |
|---|---|---|
| scan: each loop in its own helper (`split`), helpers on the slot's bytes (`subslice`), inner helpers returning bool (`bool`) | 1,287,612 each | +4,133 |
| scan: four slots written out, one helper per slot (`unrolled`, `subslice-unrolled`) | 1,282,708 | -771 |
| scan: `split` / `bool` with the per-opening helper not inlined | 1,295,084 | +11,605 |
| scan: `subslice` with the per-opening helper not inlined | 1,286,196 | +2,717 |
| scan: `unrolled` / `subslice-unrolled` with the per-opening helper not inlined | 1,283,358 / 1,282,698 | -121 / -781 |
| claim fission, no inlining attributes (R1's text as it is) | 1,282,448 | -1,031 |
| claim fission, `prepared_claim_dot` no attribute, `prepared_claim_sum` inline | 1,282,459 | -1,020 |
| claim fission, dot inline, sum not inlined | 1,283,471 | -8 |
| claim fission, dot not inlined (sum inline / no attribute / not inlined) | 1,284,392 / 1,284,368 / 1,284,368 | +913 / +889 / +889 |
| claim fission with the point loop in a block of its own | 1,283,479 | 0 (same code) |
| `prepared_claim` as in the base tree (the floor) | 1,281,611 | -1,868 |

The three texts of `prepared_claim`, relative to the base tree's own text
(lead's decision 2026-11-11: the second is adopted):

| Text | Cost | Rule | Tools |
|---|---|---|---|
| base tree's text, `if cfg!(feature="future-claim-rows")` inside the function | 0 | not allowed (`if cfg!` inside an R1 function) | not translatable |
| R1's claim-fission text (`prepared_claim_dot`, `prepared_claim_sum`), no inlining attributes | +837 | allowed (row says rewrite needed; R1's model was emitted from this text) | translates |
| pinned text under `#[cfg(not(...))]` | +1,845 | allowed | not translatable (CE03) |

Forcing the inlining either way is worse: both helpers `#[inline(always)]`
+1,868; `prepared_claim_dot` `#[inline(never)]` about +2,760; the whole
function `#[inline(never)]` about +3,400.

Why the first scan form cost 4,133: in the pinned nest the compiler keeps the
pointer to the current slot in a register and each of the 26 limb checks is a
load and a compare-and-branch; with each loop in its own helper it reloads the
slot's base from two stack slots and adds them before every second limb (47
more instructions per slot, 88 slots). With the slot index a constant at each
of four call sites the offsets are constants and the reload is gone.

Run `b4`, reference F = the candidate at that point (lane frontier loop in
the decoder, `match` in the loop; 1,281,097):

| Variant | Transfer | Variant minus F |
|---|---|---|
| `canonical_scan` pinned | 1,281,868 | +771 |
| scan in form `unrolled` (the form the tools reject) | 1,281,097 | 0 |
| lane frontier helper comparing with the empty root on every level | 1,281,184 | +87 |
| `base_lanes_tight` with `map_err` and `?` | 1,281,097 | 0 |

Runs `b5` and `b6`, the lane frontier loop:

| Form of the lane frontier loop | Transfer | Withdrawal |
|---|---|---|
| in the decoder, `match` in the loop (F; the tools reject it) | 1,281,097 | 1,287,618 |
| in the decoder, straight-line body, helper returns a flag and the node (the tools reject it) | 1,281,603 | 1,288,124 |
| in a function of its own, `match` in the loop (the final tree) | 1,281,151 | 1,287,672 |

The final tree costs 187 units more than the base on the recorded transfer
(1,281,151 against 1,280,964) and on the recorded withdrawal (1,287,672
against 1,287,485). What was measured per rewrite, each in the context of
its run: `prepared_claim` +837 against the base tree's text;
`canonical_scan` -771; `claims` +120; `Prepared::new` +8 with its helper
inlined and -112 with the helper not inlined, as adopted; `for_range` 0 for
the counting loop in place (its helper form was not measured separately);
`base_lanes_tight` 0; the lane frontier loop +54 for the function of its own
against the loop in the decoder; the program crate's other rewrites +60 in
the first batch's form (the 21 comparisons written out were not measured
separately). These do not sum to 187: the rest (the observer taken out of
the one-transaction functions, the final adapter form, the `for_range`
helpers) was not split further, on the lead's instruction not to split a
batch for a few tens of units.

### 4.3 The gate on the final tree

One run, gate name `tp1-f3`, script `fv_tp1_gate2.sh`, tree `src-tp1-b1`
(= `src-base2` + patch 0 + the batch), base tree `src-base2`, base ELF
7540abe6c5f07827011b11d3313fe5594816a32fa05963195ee4a1f5cf7856b5. One scope
(`TP-G-tp1-f3`): exit 0, wall 25:44, peak resident set 1,530,844 kB, scope
memory peak 2,294,808,576 bytes, no memory event. Time went into compilation
(the worst-case tool's target directory was cold: 353 s) and the
client-configuration tests (571 s). Gate status OK; `fv_gate_compare.py tp1-f3
BASE2` exit 0.

| Gate | Result |
|---|---|
| unit tests of the verifier crate, deployed features (they include the differential oracles: reshaped scan against the pinned scan with every limb position set to P; `for_range` against the pinned backward pass on 200 query sets; `claims` against the pinned raw-pointer form on the six saved proofs) | 56 passed, 0 failed |
| client configuration (`r1p-check`: prover on, no Aspis feature), unit tests named prover or sim | built; 15 passed, 0 failed |
| unit tests of the program crate, deployed features, both trees | 89 tests; 25 failing in the changed tree and the same 25 in the base tree (R1's two-transaction checkpoint tests); outcome lists identical |
| unit tests of the program crate, R1's features (`pool-adapter,private-leaf-salts`), both trees | 89 tests, 0 failing in both; outcome lists identical. This is the run that exercises the rewritten `authenticate_asq8_accounts` and `decode_lane_from_pool_release` on R1's own two-transaction tests |
| integration tests (nine test files, deployed features) | pass |
| SBF build, deployed features | ELF sha256 b62105e1a6392f7bae72658b88efd1ce00a9b2be7b04b6caea50c0a02a5a5e9e, 973,056 bytes (base 972,072 bytes) |
| recorded transfer replayed | 1,281,151 (base 1,280,964): 187 more; all replay conditions hold |
| recorded withdrawal replayed | 1,287,672 (base 1,287,485): 187 more; all replay conditions hold |
| redirect attempts | exit 0 |
| mutant campaign (156,704 mutants of the two recorded proofs), observer compiled in (`phase-observer`) | verdict file byte-identical to the base tree's, sha256 e3659a53d3b4e308711668d82715cd981e8d3bdc7ba859c9ff3bdaa1e3c9e2b9 |
| mutant campaign, deployed configuration (no `phase-observer`: the functions the deployed program runs) | no line with a nonzero mark count; the verdicts (file without the mark column) identical to the base tree's, sha256 a050df4712fb841d90841914f8d528fa435da5956e2ba92da29651e078c81981 |
| worst-case tool built in the changed tree, six scenarios, three marker variants each | prover output (pinned proof and re-packed proof hashes) identical to the unchanged tree in all six; no errors; changed ELF minus base ELF: 186, 184, 178, 181, 190, 182 by scenario, the same in the three variants of each |

The six worst-case scenarios, changed ELF against base ELF, heaviest marker
variant (one lamport), with the deployed Pool ELF `devnet/pool.so` (not the
changed Pool of the lead's round 10, so the absolute figures are this tool's,
not the release figure):

| Scenario | Base ELF | Final tree | Difference |
|---|---|---|---|
| withdrawal, N 255, seed 60, full | 1,328,248 | 1,328,434 | 186 |
| withdrawal, N 255, seed 1, full | 1,317,362 | 1,317,546 | 184 |
| withdrawal, N 1023, seed 1, full | 1,323,213 | 1,323,391 | 178 |
| withdrawal, N 254, seed 1, full | 1,253,628 | 1,253,809 | 181 |
| withdrawal, N 0, seed 1, genesis | 1,295,686 | 1,295,876 | 190 |
| transfer, N 255, seed 1, full | 1,309,787 | 1,309,969 | 182 |

So the two patches together cost between 178 and 190 compute units on every
measured case (187 on the two recorded payments), against a budget of 2,000
for the pass. One function is above the 300 guide: `prepared_claim`, +837
(4.2; adopted by the lead's decision). `canonical_scan` is 771 cheaper than
its pinned form.

Function comparison of the unstripped ELFs, final tree against base
(`fv_tp1_symcmp2.sh`): `.text` 939,576 to 940,344 bytes. Gone:
`canonical_scan_pinned`, `verify_finish`, `verify_observed`, `verifier::mark`,
`candidate::prepare`, `fused::verify_summed_format` (no longer on the deployed
path), `heap::uninit`, and three std helpers. New: `verify_unobserved`,
`verify_finish_unobserved`, `second_alpha`, `prepared_claim_sum`,
`prepare_summed`, `verify_summed_format_hooked`. Different size: `claims`,
`for_range`, `Prepared::new` (30,312 to 22,984 bytes: the claim sum and the
second challenge are now functions of their own), `canonical_scan` (the thunk
to 4,968 bytes), `summed_final_checks`, `fold_sums`,
`decode_lane_from_pool_release`, `stage2_owned`, and instances of
`heap::filled`, `decode_k` and `RawVec::grow_one`.

Earlier gate runs of the batch, none of them the result: `tp1-b1b` (first
batch: unit tests did not compile, wrong test filter, script overwritten
during the run; see section 8), `tp1-f1` and `tp1-f2` (stopped by hand when
the tree under them was superseded; `tp1-f1` also carried the wrong
program-test criterion).

## 5. Release-style emission of the final tree

One host scope, `TP-E70` (`fv_tp1_emit1.sh 70 TP-C70 TP-C71`): exit 0, wall
9:45, peak resident set 3,604,228 kB, scope memory peak 3,333,050,368 bytes,
no memory event. Tree `src-tp1-var`, whose two crates, aspis-core and
aspis-statement are identical to those of the gated tree `src-tp1-b1`
(checked with `diff -rq`). Second tool pair only: Charon 454586e9 (binary
sha256 57aa2359bb3e9a84480f7e4802dcdc700ef05709de30ec0eb97581b3f9c5f851),
Aeneas 0d21a9ec (binary sha256
230ee9f0c4902ea3415a01960f6887e2d4c71bc82e8b4e78dfac398da657df91). The
first pair was not run on the final tree. A translated and elaborated
function is not a verified function: nothing is proved here.

| | Verifier crate | Program crate |
|---|---|---|
| Charon run | `TP-C70`: exit 0, 493 function declarations, LLBC sha256 a1393ccd532f23040e75ca392c62ad3e83dfff73f63238c3f6634a2ef380c585 | `TP-C71`: exit 0, 297 function declarations, LLBC sha256 40e86136bd33c35e7615108e27a8a26e323e65528c6ef6d9fd69f9d082884486 |
| Features | the deployed set, with the verifier crate's own `future-lazy-horner`; overflow checks on | the list of `fv_round7.sh`; overflow checks off, as the program is built |
| Roots | `fused::verify_summed_format_unobserved` (the on-chain entry) and `verifier::checkpoint_size` (the one function of this crate that only the adapter calls) | `process_r1_cost_probe_instruction` |
| Opaque | nothing; every function of the crate that the roots reach is local | the named gaps of section 6: `close_checkpoint`, `lifecycle_init`, `lifecycle_write`, `lifecycle_finalize`, the module `deployment_ids`, the statics `AUDIT_POOL_PROGRAM` and `AUDIT_REGISTRY_PROGRAM`. Items of the verifier crate and of the library crates are boundaries of this scope |
| Aeneas without `-abort-on-error` | `TP-A70v`: exit 0, no rejection | `TP-A70p`: exit 0, no rejection |
| Aeneas with `-abort-on-error` (the release-style emission) | `TP-A70vR`: exit 0, wall 139 s, peak 2,278,320 kB | `TP-A70pR`: exit 0, wall 72 s, peak 2,999,408 kB |
| Emitted `Funs.lean` sha256 | 0fc89ebab8b0a1834d873f06bd17374d1985ea85f46bcf074b532a3426183d7c | c6122df75ff7645203c1fa70e9adbd2c112bfceb4ed0bb443dc52c42b3dfc6e4 |
| Emitted `Types.lean` sha256 | b9a21a9fb28fa20a0b1c61d4089ee448085f15d14d8fc3ad48c378ec5f5f4003 | 02f2152d0fc6c911afa686818fcdffe7174153608c30d3e1af37013e90855daa |
| Emitted `FunsExternal_Template.lean` sha256 | ec793a62a8a8573e82f8facb40907e0c71c35d2a2a5fd239666fe8515f1d8786 | f57f399aaf56b9921e0052be0b41bec87dd4664f1593301b80ce5e216d74463a |
| Emitted `TypesExternal_Template.lean` sha256 | ba5eb21eacf9da585e5938b60661d1155a6a77ae080598c769237c4de68f7af2 | 72ab24d89618642a3f9f24460da7a6887ed29045d20838e3b047a697069b1082 |
| Completeness (`TP_llbc_scan.py`): functions of the crate with a body in Charon's output | 270; 10 have no emitted definition, all of them derived `Clone` implementations or drop glue of a struct (verifier.rs 19 and 167, fused.rs 32, 147 and 155, r1_semantic.rs 7, compact.rs 71, r1_wire.rs 23 and 220, fast_pairing.rs 8) | 89; 4 have no emitted definition, all drop glue (`OwnedAccount`, `ValidatedAsqa`, `AuthenticatedAsq8Accounts`, `ScannedAsqaProof`) |
| Mutable-borrow type arguments under an erased region (the dropped-write shape) | 0 | 0 |
| Lean, modules `TypesExternal`, `Types`, `FunsExternal` | compile, 0 errors | compile, 0 errors |
| Lean, module `Funs` | 435 declarations, 3 with errors (9 error lines) | 132 declarations, 0 errors |

The scan for the dropped-write shape finds nothing by construction with this
tool pair: its Charon keeps region variables of the body and never writes an
erased region, so the scan cannot fail here. It is listed because it was
asked for; it is not evidence about written-back values.

The three failing declarations of the verifier crate are one function:
`compact::expand_values`, its loop body, and the iterator instance for
`ChunksExactMut` that the emission declares for it. The R1 library has no
model of the zipped `chunks_exact` / `chunks_exact_mut` iterators.

Counts over the 257 function rows of the table below (200 of the verifier
crate, 57 of the program crate; closures, loop bodies, derived
implementations and type declarations are not rows): 250 translate and
elaborate; 1 translates and its Lean does not elaborate
(`compact::expand_values`); 6 are opaque named gaps of the program crate
(`close_checkpoint`, the three lifecycle functions, the two program-id
statics). Not in the table because nothing reaches them any more:
`lifecycle_accounts` (its three callers are opaque), the generic
`require_distinct_accounts`, and the functions of `deployment_ids`.

"Elaborates" means: compiles with Lean 4.32.0 against the R1 (L187) library
objects after the adaptation of `tools/TP_adapt.py` with
`tools/TP_rules_release.json` (sha256
624e36d305e21f36f193944494d3398d1256efe99724716a7f5b25ecdba49f48) and with the
shim `lean/AspisTPNewLib.lean` (sha256
13f0700ef54893b0fcef4741dc76ac212b66d7efdf1f11bf8af5215873a8f81a; it compiles
with no error). The adaptation does five things and nothing else:

1. header: module-system lines to plain imports, one linter option of a newer
   Lean removed, the shim imported;
2. nine library names written with the shim's prefix (next list);
3. in `Funs` only: where a parameter or local is called `compact` or
   `weights`, references to items of the module of the same name are
   written with their full name (R1's own gate module does the same);
4. in `Funs` only: an application that the emitter split over lines at one
   column is joined into one line. The emitter formats with a margin of 80
   columns (`Translate.ml`: `Format.pp_set_margin fmt 80`, no option
   changes it); in deeply nested code its indentation reaches the limit and
   it puts a function and each argument on lines of their own at the column
   of the enclosing `let`, which Lean reads as separate statements. Twelve
   such applications are joined in the program crate, all in
   `authenticate_invariant_release_registry` (R1 text, not rewritten; without
   this step it has ten Lean errors). The step also joins 17 applications in
   the verifier crate that follow a `:=` at indentation 4, which Lean reads
   the same way joined or not.

Shim definitions needed (copied from the second pair's own library, attribute
lists omitted; none is proved here to be the right model):

| Definition | Needed by |
|---|---|
| `core.result.Result.Insts.CoreOpsTry.branch`, `…CoreOpsTry_traitFromResidualResult.from_residual`, the empty type `Never` | every function that uses `?` (the second pair's residual type is over `Never`) |
| `core.result.Result.map_err` | every `map_err` |
| `core.option.Option.ok_or` | the field decoders' callers (`ok_or(Error::…)`) |
| `core.array.from_fn` | `verify_finish_unobserved` and other `from_fn` uses |
| `core.slice.index.SliceIndexRangeFullSlice` with `core.ops.range.RangeFull` | `fused::base_lanes_tight`, the adapter's `stage2` (`&mut v[..]`) |
| `core.array.TryFromMutArraySlice.try_from` | `fused::base_lanes_tight`, `stage2` (mutable slice to mutable array reference) |
| `alloc.alloc.Global` | `r1_semantic::claims` (the allocator argument of `Vec::into_boxed_slice`) |
| `alloc.vec.Vec.is_empty` | `QueryGeometry::for_range` |

For `base_lanes_tight` and `stage2` the lead asked whether a library shim
suffices without a source change. For `stage2` it does (the two definitions
above). For `base_lanes_tight` it does not: see section 4.1; its source is
changed by one `match`.

Two std functions are axioms of the external template and have no model
anywhere: `alloc::vec::Vec::into_boxed_slice` and the conversion of a boxed
slice to a boxed array, both used by `claims` (R1's model of the rewritten
`claims` takes the same two as parameters).

### Table of the final emission

One row per function. "R1 row" quotes columns (b) and (c) of the status
table; "new gate" means the function does not exist at the pin. "Text
identical" is the final tree against c7593d23fdc. Data:
`translatability/verifier/data/final-emission/`.

| Function | Source | Translates (second pair, `-abort-on-error` run) | Lean against the R1 library | R1 row | Text identical to c7593d23fdc |
|---|---|---|---|---|---|
| `verifier::candidate::opening` | candidate.rs:29 | translates | elaborates | (b) EXTRACTED: NJS_Extract.Funs; SETTLED | (c) no | yes |
| `verifier::candidate::canonical_scan` | candidate.rs:60 | translates | elaborates | (b) EXTRACTED: NJS_Extract.Funs | (c) no (the frozen function extracts; what r | no |
| `verifier::candidate::scan_slot_base` | candidate.rs:69 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::scan_slot` | candidate.rs:77 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::scan_opening` | candidate.rs:87 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::NO_QUERY_BYTES` | candidate.rs:159 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::wide_view` | candidate.rs:161 | translates | elaborates | (b) EXTRACTED: SelectedWideViewFunsV1; NOT SETTLED | (c) no (the frozen function extracts; what r | no |
| `verifier::candidate::batch_leaf` | candidate.rs:202 | translates | elaborates | (b) EXTRACTED: NJS_Extract.Funs | (c) no (the frozen function extracts; what r | yes |
| `verifier::candidate::merkle_verdict` | candidate.rs:360 | translates | elaborates | new gate | not present at the pin |
| `compact::HEADER` | compact.rs:26 | translates | elaborates | new gate | not present at the pin |
| `compact::QUERIES` | compact.rs:28 | translates | elaborates | new gate | not present at the pin |
| `compact::SEMANTIC_ROWS` | compact.rs:29 | translates | elaborates | new gate | not present at the pin |
| `compact::LOGICAL_SEMANTIC` | compact.rs:31 | translates | elaborates | new gate | not present at the pin |
| `compact::SEMANTIC_COMPACT_VALUES` | compact.rs:33 | translates | elaborates | new gate | not present at the pin |
| `compact::COMPACT_SEMANTIC` | compact.rs:34 | translates | elaborates | new gate | not present at the pin |
| `compact::COMPACT_Y1` | compact.rs:35 | translates | elaborates | new gate | not present at the pin |
| `compact::LOGICAL_Y1` | compact.rs:36 | translates | elaborates | new gate | not present at the pin |
| `compact::OPENING` | compact.rs:37 | translates | elaborates | new gate | not present at the pin |
| `compact::OFF_SEMANTIC` | compact.rs:38 | translates | elaborates | new gate | not present at the pin |
| `compact::OFF_Y1` | compact.rs:39 | translates | elaborates | new gate | not present at the pin |
| `compact::OFF_INACTIVE` | compact.rs:40 | translates | elaborates | new gate | not present at the pin |
| `compact::OFF_ROUND0` | compact.rs:41 | translates | elaborates | new gate | not present at the pin |
| `compact::OFF_FOLDED_ROOT` | compact.rs:42 | translates | elaborates | new gate | not present at the pin |
| `compact::OFF_ROUND1` | compact.rs:43 | translates | elaborates | new gate | not present at the pin |
| `compact::OFF_FINAL` | compact.rs:44 | translates | elaborates | new gate | not present at the pin |
| `compact::FINAL_LEN` | compact.rs:45 | translates | elaborates | new gate | not present at the pin |
| `compact::OFF_OPENINGS` | compact.rs:46 | translates | elaborates | new gate | not present at the pin |
| `compact::OFF_NODES` | compact.rs:47 | translates | elaborates | new gate | not present at the pin |
| `compact::compact_row` | compact.rs:80 | translates | elaborates | (b) EXTRACTED: S1NativeCompactModelV1; SETTLED | (c) no | yes |
| `compact::expand_values` | compact.rs:131 | translates | error: Unknown constant `core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice` | (b) HAND MODEL / RECONSTRUCTED: S1ValuesOwnedModelV1 (owned-Vec index loop | (c) no (it extracts; library models missing) | yes |
| `compact::check_values` | compact.rs:140 | translates | elaborates | (b) Gate counterpart S8OwnedP6 check_values_owned (OPEN; ownership/signatu; NOT SETTLED | (c) not established | yes |
| `compact::expand_semantic` | compact.rs:154 | translates | elaborates | (b) EXTRACTED: S1NativeCompactModelV1 | (c) no (the frozen function extracts; what r | yes |
| `fast_domain::TABLE_A` | fast_domain.rs:13 | translates | elaborates | new gate | not present at the pin |
| `fast_domain::TABLE_B` | fast_domain.rs:144 | translates | elaborates | new gate | not present at the pin |
| `fast_domain::table_value` | fast_domain.rs:276 | translates | elaborates | (b) EXTRACTED: AspisR1QueryGeometryActual.Funs, NFN_ExtractedGeometry; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `fast_domain::fibre_point` | fast_domain.rs:282 | translates | elaborates | (b) EXTRACTED: AspisR1QueryGeometryActual.Funs, NFN_ExtractedGeometry; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `fast_domain::line_node` | fast_domain.rs:295 | translates | elaborates | (b) EXTRACTED: NFN_ExtractedGeometry | (c) no (the frozen function extracts; what r | yes |
| `fast_pairing::canonical::P` | fast_pairing.rs:5 | translates | elaborates | new gate | not present at the pin |
| `fast_pairing::canonical::reduce` | fast_pairing.rs:10 | translates | elaborates | (b) OPEN GAP: no key in the 1,707-key universe and no constant of this nam | (c) not established | yes |
| `fast_pairing::canonical::{fast_pairing::canonical::Q}::from_limbs` | fast_pairing.rs:24 | translates | elaborates | (b) EXTRACTED: EbyKPushExplicitTypesV1, RPz7_FIo_NativeFuns; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `fast_pairing::canonical::{fast_pairing::canonical::Q}::limbs` | fast_pairing.rs:29 | translates | elaborates | (b) EXTRACTED: RPz7_FIo_NativeFuns; SETTLED | (c) no | yes |
| `fast_pairing::canonical::{fast_pairing::canonical::Q}::from_wide` | fast_pairing.rs:33 | translates | elaborates | (b) EXTRACTED: RPz7_FIo_NativeFuns | (c) no (the frozen function extracts; what r | yes |
| `fast_pairing::canonical::{fast_pairing::canonical::Q}::raw` | fast_pairing.rs:82 | translates | elaborates | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `fast_pairing::canonical::{fast_pairing::canonical::Q}::raw::PP` | fast_pairing.rs:85 | translates | elaborates | new gate | not present at the pin |
| `fast_pairing::canonical::{fast_pairing::canonical::Dot}::new` | fast_pairing.rs:112 | translates | elaborates | (b) EXTRACTED: RPz7_FIo_NativeFuns; SETTLED | (c) no | yes |
| `fast_pairing::canonical::{fast_pairing::canonical::Dot}::push` | fast_pairing.rs:118 | translates | elaborates | (b) EXTRACTED: RPz7_FIo_NativeFuns; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `fast_pairing::canonical::{fast_pairing::canonical::Dot}::finish` | fast_pairing.rs:123 | translates | elaborates | (b) EXTRACTED: RPz7_FIo_NativeFuns; SETTLED | (c) no | yes |
| `fast_pairing::canonical::{fast_pairing::canonical::Dot}::value` | fast_pairing.rs:125 | translates | elaborates | new gate | not present at the pin |
| `fast_pairing::MAX_TERMS` | fast_pairing.rs:149 | translates | elaborates | new gate | not present at the pin |
| `fast_pairing::limbs_of` | fast_pairing.rs:152 | translates | elaborates | (b) EXTRACTED: RPz7_FIo_NativeFuns; SETTLED | (c) no | yes |
| `fast_pairing::checked_q` | fast_pairing.rs:157 | translates | elaborates | (b) EXTRACTED: RPz7_FIo_NativeFuns; SETTLED | (c) no | yes |
| `fast_pairing::qm31_of` | fast_pairing.rs:162 | translates | elaborates | (b) OPEN GAP: no key in the 1,707-key universe and no constant of this nam | (c) not established | yes |
| `fast_pairing::{fast_pairing::EbyKDot}::new` | fast_pairing.rs:179 | translates | elaborates | (b) EXTRACTED: RPz7_FIo_NativeFuns; SETTLED | (c) no | yes |
| `fast_pairing::{fast_pairing::EbyKDot}::push` | fast_pairing.rs:185 | translates | elaborates | (b) EXTRACTED: RPz7_FIo_NativeFuns; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `fast_pairing::{fast_pairing::EbyKDot}::finish` | fast_pairing.rs:215 | translates | elaborates | (b) EXTRACTED: RPz7_FIo_NativeFuns; SETTLED | (c) no | yes |
| `fast_pairing::{fast_pairing::EbyKDot}::value` | fast_pairing.rs:224 | translates | elaborates | new gate | not present at the pin |
| `fast_pairing::{fast_pairing::KbyKDot}::new` | fast_pairing.rs:282 | translates | elaborates | (b) EXTRACTED: RPz7_FIo_NativeFuns; SETTLED | (c) no | yes |
| `fast_pairing::{fast_pairing::KbyKDot}::push` | fast_pairing.rs:288 | translates | elaborates | (b) EXTRACTED: RPz7_FIo_NativeFuns; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `fast_pairing::{fast_pairing::KbyKDot}::finish` | fast_pairing.rs:315 | translates | elaborates | (b) EXTRACTED: RPz7_FIo_NativeFuns; SETTLED | (c) no | yes |
| `fast_pairing::{fast_pairing::KbyKDot}::value` | fast_pairing.rs:321 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::{verifier::candidate::fused::Hook}::NONE` | fused.rs:38 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::{verifier::candidate::fused::Hook}::note` | fused.rs:58 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::P64` | fused.rs:63 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::NO_BYTES` | fused.rs:124 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::relation_view` | fused.rs:125 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::coefficients` | fused.rs:169 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::scanned_k` | fused.rs:241 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::extension_lane` | fused.rs:251 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::push_k4` | fused.rs:268 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::push_e4` | fused.rs:275 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::push_e` | fused.rs:281 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::finish_e4` | fused.rs:285 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::first_fold_base` | fused.rs:291 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::first_fold_extension` | fused.rs:299 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::second_fold` | fused.rs:308 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::cubic` | fused.rs:342 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::fold_sums` | fused.rs:349 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::k_of` | fused.rs:413 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::base_query` | fused.rs:432 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::base_fold` | fused.rs:461 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::base_accumulate` | fused.rs:476 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::base_lanes_tight` | fused.rs:497 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::CERTIFICATE_BYTES` | fused.rs:586 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::ROW_CLAIMS` | fused.rs:587 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::ROW_ROUND` | fused.rs:588 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::summed_final_checks` | fused.rs:627 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::final_rounds` | fused.rs:657 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::final_message_at` | fused.rs:671 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::claims_bytes` | fused.rs:677 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::equality_tables` | fused.rs:692 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::query_weight_mle_pairs` | fused.rs:744 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::summed_format::MAGIC` | fused.rs:842 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::summed_format::SLOT_NODES` | fused.rs:845 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::summed_format::OFF_NODES` | fused.rs:846 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::summed_format::slot_offset` | fused.rs:850 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::summed_format::OFF_CERTIFICATE` | fused.rs:856 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::summed_format::PROOF_BYTES` | fused.rs:857 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::parse_shape_summed` | fused.rs:864 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::merged_keys` | fused.rs:879 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::merged_tree` | fused.rs:901 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::merged_merkle` | fused.rs:921 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::verify_summed_format_hooked` | fused.rs:933 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::verify_summed_format_unobserved` | fused.rs:972 | translates | elaborates | new gate | not present at the pin |
| `verifier::candidate::fused::prepare_summed` | fused.rs:979 | translates | elaborates | new gate | not present at the pin |
| `program::{impl aspis_core::digest::Digest32 for program::SolanaDigest}` | lib.rs:11 | translates | elaborates | new gate | not present at the pin |
| `program::{impl aspis_core::digest::Digest32 for program::SolanaDigest}::digest` | lib.rs:13 | translates | elaborates | no row | yes |
| `program::{impl aspis_core::digest::Digest32 for program::SolanaDigest}::digest_into` | lib.rs:20 | translates | elaborates | new gate | not present at the pin |
| `program::error` | lib.rs:55 | translates | elaborates | no row | yes |
| `program::process_r1_cost_probe_instruction` | lib.rs:72 | translates | elaborates | (b) Entry point. With `pool-adapter` only the adapter arm is compiled: `po | (c) no for the emission; it is uncompiled fo | yes |
| `multiproof::LEAF_BITS` | multiproof.rs:18 | translates | elaborates | new gate | not present at the pin |
| `multiproof::BINARY_NODE_TAG` | multiproof.rs:21 | translates | elaborates | new gate | not present at the pin |
| `multiproof::MAX_MERGED` | multiproof.rs:300 | translates | elaborates | new gate | not present at the pin |
| `multiproof::well_formed_merged` | multiproof.rs:309 | translates | elaborates | new gate | not present at the pin |
| `multiproof::verify_counting_merged` | multiproof.rs:366 | translates | elaborates | new gate | not present at the pin |
| `multiproof::merged_level` | multiproof.rs:403 | translates | elaborates | new gate | not present at the pin |
| `program::pool_route::CLOSE_CHECKPOINT_TAG` | pool_route.rs:6 | translates | elaborates | new gate | not present at the pin |
| `program::pool_route::is_close_checkpoint` | pool_route.rs:9 | translates | elaborates | (b) PIN2-new. Same PCXQ_E002 emission; tagged OFF_EMISSION_WRAPPING (`data; NOT SETTLED | (c) no | yes |
| `program::pool_route::admitted` | pool_route.rs:16 | translates | elaborates | (b) PIN2-changed. PCXQ_E002 emission (Charon daad69be + Aeneas 959659a6, p; NOT SETTLED | (c) no (it extracts) | yes |
| `program::r1_pool_adapter::CHECKPOINT_TAIL_BYTES` | r1_pool_adapter.rs:54 | translates | elaborates | new gate | not present at the pin |
| `program::r1_pool_adapter::PROFILE_BINDING` | r1_pool_adapter.rs:68 | translates | elaborates | new gate | not present at the pin |
| `program::r1_pool_adapter::RELEASE_BINDING` | r1_pool_adapter.rs:73 | translates | elaborates | new gate | not present at the pin |
| `program::r1_pool_adapter::AUDIT_POOL_PROGRAM` | r1_pool_adapter.rs:80 | axiom (opaque or body rejected) |  | new gate | not present at the pin |
| `program::r1_pool_adapter::AUDIT_REGISTRY_PROGRAM` | r1_pool_adapter.rs:84 | axiom (opaque or body rejected) |  | new gate | not present at the pin |
| `program::r1_pool_adapter::pool_program_id` | r1_pool_adapter.rs:89 | translates | elaborates | (b) HAND MODEL / TRUST: op45. `deployment_ids::deployment_id` is CE18 (Aen | (c) n/a (HM-A by owner decision) | yes |
| `program::r1_pool_adapter::registry_program_id` | r1_pool_adapter.rs:94 | translates | elaborates | (b) Same mechanism as pool_program_id (deployment_ids::deployment_id, CE18 | (c) n/a (HM-A) | yes |
| `program::r1_pool_adapter::AUDIT_POLICY_BINDING` | r1_pool_adapter.rs:97 | translates | elaborates | new gate | not present at the pin |
| `program::r1_pool_adapter::PAIR_FOREST_MASTER_SEED` | r1_pool_adapter.rs:99 | translates | elaborates | new gate | not present at the pin |
| `program::r1_pool_adapter::PAIR_FOREST_LANE_SEED` | r1_pool_adapter.rs:100 | translates | elaborates | new gate | not present at the pin |
| `program::r1_pool_adapter::PAIR_FOREST_CHECKPOINT_SEED` | r1_pool_adapter.rs:101 | translates | elaborates | new gate | not present at the pin |
| `program::r1_pool_adapter::VERIFIER_REGISTRY_SEED` | r1_pool_adapter.rs:102 | translates | elaborates | new gate | not present at the pin |
| `program::r1_pool_adapter::VERIFIER_ENTRY_SEED` | r1_pool_adapter.rs:103 | translates | elaborates | new gate | not present at the pin |
| `program::r1_pool_adapter::VERIFIER_REGISTRY_V2_SEED` | r1_pool_adapter.rs:104 | translates | elaborates | new gate | not present at the pin |
| `program::r1_pool_adapter::VERIFIER_ENTRY_V2_SEED` | r1_pool_adapter.rs:105 | translates | elaborates | new gate | not present at the pin |
| `program::r1_pool_adapter::readonly_meta_ok` | r1_pool_adapter.rs:170 | translates | elaborates | (b) EXTRACTED: AdapterRwModel | (c) no (the frozen function extracts; what r | yes |
| `program::r1_pool_adapter::readonly_buffer_meta_ok` | r1_pool_adapter.rs:191 | translates | elaborates | (b) EXTRACTED: AdapterRwModel; SETTLED | (c) no | yes |
| `program::r1_pool_adapter::lifecycle_init` | r1_pool_adapter.rs:343 | axiom (opaque or body rejected) |  | (b) OFF THE ADMITTED SURFACE. It is compiled, and `process` still routes t | (c) n/a (unreachable under `admitted`) | yes |
| `program::r1_pool_adapter::lifecycle_write` | r1_pool_adapter.rs:368 | axiom (opaque or body rejected) |  | (b) OFF THE ADMITTED SURFACE. It is compiled, and `process` still routes t | (c) n/a (unreachable under `admitted`) | yes |
| `program::r1_pool_adapter::lifecycle_finalize` | r1_pool_adapter.rs:405 | axiom (opaque or body rejected) |  | (b) OFF THE ADMITTED SURFACE. It is compiled, and `process` still routes t | (c) n/a (unreachable under `admitted`) | yes |
| `program::r1_pool_adapter::decode_master_box` | r1_pool_adapter.rs:429 | translates | elaborates | (b) EXTRACTED wrapper: op48, PROVED_CONDITIONAL (PCVV slot48; fresh E008) ; NOT SETTLED | (c) yes (raw decoder CE15) | yes |
| `program::r1_pool_adapter::decode_checkpoint_box` | r1_pool_adapter.rs:437 | translates | elaborates | (b) EXTRACTED wrapper: op49, PROVED_CONDITIONAL (PCVV slot49). NKY-RT216 (; NOT SETTLED | (c) yes (raw decoder CE15) | yes |
| `program::r1_pool_adapter::lane_frontier_node` | r1_pool_adapter.rs:447 | translates | elaborates | new gate | not present at the pin |
| `program::r1_pool_adapter::lane_frontier` | r1_pool_adapter.rs:474 | translates | elaborates | new gate | not present at the pin |
| `program::r1_pool_adapter::decode_lane_from_pool_release` | r1_pool_adapter.rs:492 | translates | elaborates | (b) CANNOT-EXTRACT (PCXN_CANNOT_EXTRACT.json CE01): op50, "Early returns i | (c) yes | no |
| `program::r1_pool_adapter::scan_proof_buffer` | r1_pool_adapter.rs:844 | translates | elaborates | (b) EXTRACTED: op51, PROVED_CONDITIONAL (PCVV slot51, PRVEq_AdapterCallees; NOT SETTLED | (c) no | yes |
| `program::r1_pool_adapter::asq8_common` | r1_pool_adapter.rs:875 | translates | elaborates | (b) EXTRACTED: AspisR1AdapterReconstruct.Funs; SETTLED | (c) no | yes |
| `program::r1_pool_adapter::transfer_statement_box` | r1_pool_adapter.rs:894 | translates | elaborates | (b) EXTRACTED: AspisR1AdapterReconstruct.Funs, AspisR1AdapterReconstruct.T | (c) no (the frozen function extracts; what r | yes |
| `program::r1_pool_adapter::withdrawal_statement_box` | r1_pool_adapter.rs:908 | translates | elaborates | (b) EXTRACTED: AspisR1AdapterReconstruct.Funs, AspisR1AdapterReconstruct.T | (c) no (the frozen function extracts; what r | yes |
| `program::r1_pool_adapter::reconstruct_asq8_statement` | r1_pool_adapter.rs:922 | translates | elaborates | (b) EXTRACTED: op52, PROVED_AT_GATE_LEVEL (PCVV slot52; fresh PCWE_E001, O; NOT SETTLED | (c) no | yes |
| `program::r1_pool_adapter::emit_result` | r1_pool_adapter.rs:988 | translates | elaborates | (b) NO EMISSION: op53, BLOCKED_NO_FROZEN_EMISSION. Deployed slot = LIBB_Po | (c) not established (no extraction attempt r | yes |
| `program::r1_pool_adapter::close_checkpoint` | r1_pool_adapter.rs:1025 | axiom (opaque or body rejected) |  | (b) CANNOT-EXTRACT (PIN2_CANNOT_EXTRACT.json): `let [checkpoint, base] = a | (c) yes (or an Aeneas fix for PtrMetadata on | yes |
| `program::r1_pool_adapter::process` | r1_pool_adapter.rs:1060 | translates | elaborates | (b) PIN2-changed (new arm 7 to close_checkpoint). PCXQ_E002 emission (T0, ; NOT SETTLED | (c) no | yes |
| `program::r1_pool_adapter::owned::{program::r1_pool_adapter::owned::OwnedAccount}::key` | r1_pool_adapter_owned.rs:19 | translates | elaborates | (b) Accessors inside the stage transcriptions and the AdapterRw ops. No se | (c) no (trivial accessor) | yes |
| `program::r1_pool_adapter::owned::{program::r1_pool_adapter::owned::OwnedAccount}::owner` | r1_pool_adapter_owned.rs:20 | translates | elaborates | (b) Accessors inside the stage transcriptions and the AdapterRw ops. No se | (c) no (trivial accessor) | yes |
| `program::r1_pool_adapter::owned::{program::r1_pool_adapter::owned::OwnedAccount}::data` | r1_pool_adapter_owned.rs:21 | translates | elaborates | (b) EXTRACTED: NMT_stage1_owned `OwnedAccount.data` DEPENDS_ON_LIBRARY_TRU | (c) no | yes |
| `program::r1_pool_adapter::owned::{program::r1_pool_adapter::owned::OwnedAccount}::data_len` | r1_pool_adapter_owned.rs:24 | translates | elaborates | (b) Accessors inside the stage transcriptions and the AdapterRw ops. No se | (c) no (trivial accessor) | yes |
| `program::r1_pool_adapter::owned::snapshot` | r1_pool_adapter_owned.rs:29 | translates | elaborates | (b) Inside the stage1/stage2 transcription windows (TX1:344 / TX2:240). No | (c) yes (with stage1/stage2, CE20/CE21) | yes |
| `program::r1_pool_adapter::owned::require_readonly_buffer` | r1_pool_adapter_owned.rs:45 | translates | elaborates | (b) EXTRACTED: AdapterRwModel EQUALITY_PROVED_JOB. SETTLED. | (c) no | yes |
| `program::r1_pool_adapter::owned::require_readonly_account` | r1_pool_adapter_owned.rs:48 | translates | elaborates | (b) EXTRACTED: AdapterRwModel DEPENDS_ON_LIBRARY_TRUST (HM row). Other (no | (c) no | yes |
| `program::r1_pool_adapter::owned::require_verifier_checkpoint` | r1_pool_adapter_owned.rs:51 | translates | elaborates | (b) EXTRACTED: AdapterRwModel CONDITIONAL_ON_BINDING. NOT SETTLED.; NOT SETTLED | (c) no | yes |
| `program::r1_pool_adapter::owned::require_distinct_seven` | r1_pool_adapter_owned.rs:75 | translates | elaborates | new gate | not present at the pin |
| `program::r1_pool_adapter::owned::authenticate_invariant_release_registry` | r1_pool_adapter_owned.rs:149 | translates | elaborates | (b) EXTRACTED gate (AdapterRwModel) OPEN. Its decoder callees are covered ; NOT SETTLED | (c) no for the body; see the decoders | yes |
| `program::r1_pool_adapter::owned::authenticate_asq8_accounts` | r1_pool_adapter_owned.rs:298 | translates | elaborates | (b) EXTRACTED: AdapterRwModel `authenticate_asq8_accounts` CONDITIONAL_ON_; NOT SETTLED | (c) yes (through CE14 callee) | no |
| `program::r1_pool_adapter::owned::validate_asq8` | r1_pool_adapter_owned.rs:411 | translates | elaborates | (b) EXTRACTED: AdapterRwModel `validate_asq8` CONDITIONAL_ON_BINDING; PCVV; NOT SETTLED | (c) yes (through CE14 callee) | yes |
| `program::r1_pool_adapter::owned::stage2_owned` | r1_pool_adapter_owned.rs:523 | translates | elaborates | (b) EXTRACTED: AdapterRwModel `stage2_owned` CONDITIONAL_ON_BINDING; PCVV_; NOT SETTLED | (c) yes (through CE14 callee) | yes |
| `program::r1_pool_adapter::owned::stage1` | r1_pool_adapter_owned.rs:588 | translates | elaborates | (b) HAND MODEL: ReviewedTranscription-TX1:344 (ruling (bn)), now OPEN_TRAN | (c) yes | yes |
| `program::r1_pool_adapter::owned::stage2` | r1_pool_adapter_owned.rs:620 | translates | elaborates | (b) HAND MODEL: ReviewedTranscription-TX2:240 (ruling (bn)), OPEN_TRANSCRI | (c) yes | yes |
| `r1_semantic::claims` | r1_semantic.rs:42 | translates | elaborates | (b) CANNOT-EXTRACT (PCXN_CANNOT_EXTRACT.json CE12): Aeneas CFailure on the; NOT SETTLED | (c) yes | no |
| `r1_semantic::public_transcript` | r1_semantic.rs:101 | translates | elaborates | (b) EXTRACTED at PIN2: PIN2_NEWGATE_r1_semantic (PCXU_E003, Charon 454586e; NOT SETTLED | (c) no | yes |
| `r1_semantic::semantic_boundary` | r1_semantic.rs:135 | translates | elaborates | (b) CANNOT-EXTRACT (PCXN_CANNOT_EXTRACT.json CE11): same Iterator trait-ty; NOT SETTLED | (c) yes | yes |
| `r1_semantic::semantic_value` | r1_semantic.rs:197 | translates | elaborates | (b) EXTRACTED: AspisR1SemanticCallExtraction keys OPEN. 14k: "emitted but  | (c) no (library models missing; not a constr | yes |
| `r1_semantic::semantic_round` | r1_semantic.rs:205 | translates | elaborates | (b) No key. It is called only from semantic_rounds (CE13), and the record  | (c) not established | yes |
| `r1_semantic::semantic_rounds` | r1_semantic.rs:242 | translates | elaborates | (b) CANNOT-EXTRACT (PCXN_CANNOT_EXTRACT.json CE13): same crash. No key. NO; NOT SETTLED | (c) yes | yes |
| `r1_semantic::verify_unobserved` | r1_semantic.rs:432 | translates | elaborates | new gate | not present at the pin |
| `r1_semantic::verify_finish_unobserved` | r1_semantic.rs:441 | translates | elaborates | new gate | not present at the pin |
| `r1_wire::DOMAIN` | r1_wire.rs:12 | translates | elaborates | new gate | not present at the pin |
| `r1_wire::LANES` | r1_wire.rs:13 | translates | elaborates | new gate | not present at the pin |
| `r1_wire::POINTS` | r1_wire.rs:14 | translates | elaborates | new gate | not present at the pin |
| `r1_wire::CLAIMS` | r1_wire.rs:15 | translates | elaborates | new gate | not present at the pin |
| `r1_wire::row_shape` | r1_wire.rs:39 | translates | elaborates | (b) EXTRACTED: AspisR1PrefixAggregateParser.Funs, AspisR1RecordParser.Funs; SETTLED | (c) no | yes |
| `r1_wire::validate_record_fields` | r1_wire.rs:53 | translates | elaborates | (b) EXTRACTED: AspisR1PrefixAggregateParser.Funs, AspisR1RecordParser.Funs; SETTLED | (c) no | yes |
| `r1_wire::parse_record` | r1_wire.rs:147 | translates | elaborates | (b) EXTRACTED: AspisR1PrefixAggregateParser.Funs, AspisR1RecordParser.Funs; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `r1_wire::validated_values` | r1_wire.rs:202 | translates | elaborates | new gate | not present at the pin |
| `r1_wire::validated_limb` | r1_wire.rs:213 | translates | elaborates | new gate | not present at the pin |
| `r1_wire::{r1_wire::ValidatedRecord<'a>}::row` | r1_wire.rs:227 | translates | elaborates | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `r1_wire::{r1_wire::ValidatedRecord<'a>}::framed` | r1_wire.rs:231 | translates | elaborates | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `r1_wire::{r1_wire::ValidatedRecord<'a>}::payload` | r1_wire.rs:235 | translates | elaborates | (b) EXTRACTED: AspisR1DecodeKFullV10.Funs; SETTLED | (c) no | yes |
| `r1_wire::{r1_wire::ValidatedRecord<'a>}::decode_k` | r1_wire.rs:277 | translates | elaborates | (b) CANNOT-EXTRACT (PCXN_CANNOT_EXTRACT.json CE04): "Joining region abstra | (c) yes | yes |
| `r1_wire::{r1_wire::SemanticTranscript<H>}::new` | r1_wire.rs:317 | translates | elaborates | (b) EXTRACTED: AspisR1PublicPreparation.Types; SETTLED | (c) no | yes |
| `r1_wire::{r1_wire::SemanticTranscript<H>}::state` | r1_wire.rs:325 | translates | elaborates | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `r1_wire::{r1_wire::SemanticTranscript<H>}::sample_block_validated` | r1_wire.rs:332 | translates | elaborates | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `r1_wire::{r1_wire::SemanticTranscript<H>}::semantic_validated` | r1_wire.rs:358 | translates | elaborates | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `r1_wire::{r1_wire::SemanticTranscript<H>}::circle_validated` | r1_wire.rs:371 | translates | elaborates | (b) OPEN GAP: no key in the 1,707-key universe and no constant of this nam | (c) not established | yes |
| `r1_wire::parse_record_at` | r1_wire.rs:416 | translates | elaborates | (b) EXTRACTED: AspisR1PrefixAggregateParser.Funs; SETTLED | (c) no | yes |
| `r1_wire::{r1_wire::Prefix<'a>}::parse` | r1_wire.rs:430 | translates | elaborates | (b) EXTRACTED: AspisR1PrefixAggregateParser.Funs; SETTLED | (c) no | yes |
| `r1_wire::{r1_wire::Prefix<'a>}::record` | r1_wire.rs:476 | translates | elaborates | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `r1_wire::{r1_wire::Prefix<'a>}::payload` | r1_wire.rs:482 | translates | elaborates | (b) EXTRACTED: AspisR1DecodeKFullV10.Funs; SETTLED | (c) no | yes |
| `r1_wire::{r1_wire::Prefix<'a>}::validated_record` | r1_wire.rs:486 | translates | elaborates | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `r1_wire::begin` | r1_wire.rs:528 | translates | elaborates | (b) EXTRACTED: AspisR1PublicPreparation(+PIN2) constants and PIN2_NEWGATE_ | (c) no | yes |
| `sampler::qm31_div_pass` | sampler.rs:11 | translates | elaborates | (b) EXTRACTED: AspisR1Post25Sampler.Funs, AspisR1Qm31SamplerIndex.Funs; SETTLED | (c) yes (the current model is a rewritten cr | yes |
| `sampler::qm31_digits` | sampler.rs:24 | translates | elaborates | (b) EXTRACTED: AspisR1Qm31SamplerIndex.Funs; SETTLED | (c) no | yes |
| `sampler::qm31_sample` | sampler.rs:45 | translates | elaborates | (b) EXTRACTED: AspisR1Qm31SamplerIndex `qm31_sample` EQUALITY_PROVED_JOB,  | (c) no | yes |
| `sampler::low_base_p_digits` | sampler.rs:70 | translates | elaborates | (b) REWRITTEN-CRATE EMISSION: AspisR1Post25Sampler.Funs (crate `r1_post25_ | (c) yes | no |
| `sampler::decode8` | sampler.rs:92 | translates | elaborates | (b) EXTRACTED: AspisR1Post25Sampler.Funs; SETTLED | (c) yes (the current model is a rewritten cr | yes |
| `sampler::add_small_base_p` | sampler.rs:113 | translates | elaborates | (b) REWRITTEN-CRATE EMISSION: AspisR1Post25SamplerIndexedAddSmallCandidate | (c) no by construct (the frozen form emits c | no |
| `sampler::ordinary_sample` | sampler.rs:125 | translates | elaborates | (b) REWRITTEN-CRATE EMISSION: AspisR1Post25Sampler `ordinary_sample` OPEN ; NOT SETTLED | (c) yes (through low_base_p_digits) | yes |
| `sampler::gamma_sample` | sampler.rs:134 | translates | elaborates | (b) REWRITTEN-CRATE EMISSION: GammaCallerExplicitHelpers (`aspis_r1_stage2; NOT SETTLED | (c) yes (through low_base_p_digits; the gamm | yes |
| `sampler::circle_sample` | sampler.rs:144 | translates | elaborates | (b) REWRITTEN-CRATE EMISSION: RPz7_AspisR1CircleSampleWrapper_Funs (`r1_ci; NOT SETTLED | (c) not established (no frozen extraction at | yes |
| `trace::value` | trace.rs:6 | translates | elaborates | (b) EXTRACTED: FIo_Native `trace.value` EQUALITY_PROVED (PRVEq.RPz7_FIo_Na | (c) no | yes |
| `transcript::{transcript::Transcript<H>}::new` | transcript.rs:7 | translates | elaborates | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `transcript::{transcript::Transcript<H>}::resume` | transcript.rs:18 | translates | elaborates | new gate | not present at the pin |
| `transcript::{transcript::Transcript<H>}::absorb` | transcript.rs:19 | translates | elaborates | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `transcript::{transcript::Transcript<H>}::block` | transcript.rs:22 | translates | elaborates | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `transcript::{transcript::Transcript<H>}::scalar` | transcript.rs:28 | translates | elaborates | (b) No key in the 1,707 universe and no constant of this name in the cone. | (c) not established | yes |
| `transcript::{transcript::Transcript<H>}::scalar_k` | transcript.rs:36 | translates | elaborates | (b) No key in the 1,707 universe and no constant of this name in the cone. | (c) not established | yes |
| `transcript::{transcript::Transcript<H>}::queries` | transcript.rs:40 | translates | elaborates | (b) EXTRACTED: AspisR1PublicPreparation `transcript.Transcript.queries` co | (c) no | yes |
| `transport::TAU` | transport.rs:4 | translates | elaborates | new gate | not present at the pin |
| `transport::{transport::Variant}::tag` | transport.rs:6 | translates | elaborates | (b) EXTRACTED: NJS_Extract.Funs, Op3I_Source; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `transport::{transport::Variant}::folds` | transport.rs:8 | translates | elaborates | (b) EXTRACTED: FinishCandidateExplicitOps; SETTLED | (c) no | yes |
| `transport::{transport::Variant}::final_len` | transport.rs:9 | translates | elaborates | (b) OPEN GAP: no key in the 1,707-key universe and no constant of this nam | (c) not established | yes |
| `program::r1_pool_adapter::v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS` | v7_pair_empty_roots.rs:14 | translates | elaborates | new gate | not present at the pin |
| `verifier::SEMANTIC_BYTES` | verifier.rs:8 | translates | elaborates | new gate | not present at the pin |
| `verifier::CHECKPOINT_FIXED` | verifier.rs:18 | translates | elaborates | new gate | not present at the pin |
| `verifier::checkpoint_size` | verifier.rs:32 | translates | elaborates | (b) OPEN GAP: no key in the 1,707-key universe and no constant of this nam | (c) not established | yes |
| `verifier::echeck` | verifier.rs:40 | translates | elaborates | (b) HAND MODEL: ReviewedTranscription NJZ-RT189 (REACHED, NJZ_native.patch | (c) not established (no fresh extraction rec | yes |
| `verifier::prepared_claim_sum` | verifier.rs:56 | translates | elaborates | new gate | not present at the pin |
| `verifier::prepared_claim_dot` | verifier.rs:63 | translates | elaborates | new gate | not present at the pin |
| `verifier::prepared_claim` | verifier.rs:73 | translates | elaborates | (b) CANNOT-EXTRACT (PCXN_CANNOT_EXTRACT.json CE03): "Returns inside of nes; NOT SETTLED | (c) yes | no |
| `verifier::second_alpha` | verifier.rs:102 | translates | elaborates | new gate | not present at the pin |
| `verifier::{verifier::Prepared}::new` | verifier.rs:112 | translates | elaborates | (b) CANNOT-EXTRACT (PCXN_CANNOT_EXTRACT.json CE03): "Unreachable" at verif; NOT SETTLED | (c) yes | yes |
| `verifier::batch_prefix_products` | verifier.rs:174 | translates | elaborates | (b) EXTRACTED: NFN_ExtractedGeometry, Port4C_NativePrefix; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `verifier::batch_suffix_inverses` | verifier.rs:191 | translates | elaborates | new gate | not present at the pin |
| `verifier::group_inverses` | verifier.rs:204 | translates | elaborates | new gate | not present at the pin |
| `verifier::{verifier::QueryGeometry}::for_range` | verifier.rs:216 | translates | elaborates | (b) EXTRACTED: NFN_ExtractedGeometry, Port3_NativeGeometryBody, Stage2Cont; NOT SETTLED | (c) no (the frozen function extracts; what r | no |
| `verifier::{verifier::QueryGeometry}::for_query` | verifier.rs:237 | translates | elaborates | (b) OPEN GAP: no key in the 1,707-key universe and no constant of this nam | (c) not established | yes |
| `verifier::polynomial` | verifier.rs:389 | translates | elaborates | (b) HAND MODEL: ReviewedTranscription-polynomial (TX2:119; NHE_Polynomial  | (c) not established (`(0..7).rev().fold`: Re | yes |
| `verifier::finish_relation_round` | verifier.rs:390 | translates | elaborates | (b) EXTRACTED: FinishCandidateExplicitOps; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `weights::QUARTER` | weights.rs:5 | translates | elaborates | new gate | not present at the pin |
| `weights::PERM` | weights.rs:6 | translates | elaborates | new gate | not present at the pin |
| `weights::powers` | weights.rs:11 | translates | elaborates | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `weights::double` | weights.rs:24 | translates | elaborates | (b) OPEN GAP: no key in the 1,707-key universe and no constant of this nam | (c) not established | yes |
| `weights::field` | weights.rs:25 | translates | elaborates | (b) EXTRACTED: WeightsFieldExplicitDecoder; SETTLED | (c) no | yes |
| `weights::S2_INACTIVE_GROUPS` | weights.rs:29 | translates | elaborates | new gate | not present at the pin |
| `weights::S2_INACTIVE_MASKS` | weights.rs:30 | translates | elaborates | new gate | not present at the pin |
| `weights::factored_s2_libra_weights` | weights.rs:108 | translates | elaborates | (b) MODELLED, NO PROVENANCE KEY: no key in the 1,707-key universe, but con | (c) not established | yes |
| `weights::{weights::Weights}::box_from_parts` | weights.rs:202 | translates | elaborates | (b) OPEN GAP: no key in the 1,707-key universe and no constant of this nam | (c) not established | yes |
| `weights::{weights::Weights}::new` | weights.rs:210 | translates | elaborates | (b) OPEN GAP: no key in the 1,707-key universe and no constant of this nam | (c) not established | yes |
| `weights::{weights::Weights}::scalar_factor` | weights.rs:237 | translates | elaborates | (b) EXTRACTED: RPz7_FIo_NativeTypes; NOT SETTLED | (c) no (the frozen function extracts; what r | yes |
| `weights::{weights::Weights}::row_product` | weights.rs:374 | translates | elaborates | new gate | not present at the pin |
| `weights::{weights::Weights}::product_rows::KINDS` | weights.rs:381 | translates | elaborates | new gate | not present at the pin |
| `weights::{weights::Weights}::product_rows` | weights.rs:382 | translates | elaborates | new gate | not present at the pin |
| `weights::{weights::Weights}::inactive_tensor` | weights.rs:392 | translates | elaborates | new gate | not present at the pin |
| `weights::{weights::Weights}::mle_at` | weights.rs:401 | translates | elaborates | new gate | not present at the pin |
| `weights::inactive_groups` | weights.rs:416 | translates | elaborates | new gate | not present at the pin |
| `weights::kappa_sum` | weights.rs:421 | translates | elaborates | new gate | not present at the pin |
| `weights::digit_dot` | weights.rs:426 | translates | elaborates | new gate | not present at the pin |
| `weights::perm_dot` | weights.rs:431 | translates | elaborates | new gate | not present at the pin |
| `weights::libra_at` | weights.rs:436 | translates | elaborates | new gate | not present at the pin |

## 6. Named gaps

Functions of the two crates that the one-transaction entry reaches and that
are not translated, or translated and not elaborated, after the two patches.
None was forced.

| Function | State | Why it is left |
|---|---|---|
| `r1_pool_adapter::close_checkpoint` (R1, PIN2) | does not translate; pinned text kept | Account plumbing. The tools first reject the slice pattern over the accounts ("Inconsistent projection: PtrMetadata"). With the pattern replaced by a length test and indexing (tried, emission `TP-A31p`) they stop at the next thing: the function writes lamports and data through the SDK's `RefCell` handles (`try_borrow_mut_lamports`, `try_borrow_mut_data`), "Unreachable". No loop-form change removes that. It IS reachable in the deployed program: `pool_route::admitted` admits `[7, len, seed]`. A payment reaches it in its closing transaction, after settlement: the client's close plan (`tools/r1-cost-probe/src/bin/devnet_spend/Pin2_upload.rs`, `close_plan`, read not run) builds one transaction of three instructions, two closes of the upload program's proof accounts and this instruction to the verifier, which zeroes the checkpoint account and moves its lamports to the base account (the payer in that plan). |
| `r1_pool_adapter::lifecycle_accounts` (R1) | does not translate; pinned text kept | Account plumbing. Same slice pattern; with it replaced the tools reject the function as a whole ("Unreachable"): it returns two references to account handles. The first tool pair names the cause: "Instantiating the type parameters of a function with types containing mutable borrows is currently not allowed". |
| `r1_pool_adapter::lifecycle_init`, `lifecycle_write`, `lifecycle_finalize` (R1) | their bodies translate (emission `TP-A40p`); the Lean does not elaborate there because they call `lifecycle_accounts`, whose emitted declaration has no body; opaque in the release-style emission | All three cannot run in the deployed program: `pool_route::admitted` (pinned text) admits only `[3, 10]`, `[3, 11]`, data starting with `ASQ8`, and the checkpoint close, and it is tested before `process`; tags 4, 5 and 6 are rejected there. |
| `r1_pool_adapter_owned::require_distinct_accounts` (R1) | does not translate; pinned text kept; no longer reached from the one-transaction entry | The generic form loops over an array of references. Its seven-account call is replaced by the written-out `require_distinct_seven`; its three-account call is in `stage1_owned`, which the one-transaction entry does not reach. |
| `r1_pool_adapter::deployment_ids::program_id`, `deployment_id`, `AUDIT_POOL_PROGRAM`, `AUDIT_REGISTRY_PROGRAM` | do not translate | Compile-time decoding of the program identifiers ("Early returns inside of loops", "Internal error"). R1 has the same gap (CE18). Not attempted. |
| `compact::expand_values` (R1) | translates; the Lean does not elaborate | Library models missing in the R1 library: the zipped `chunks_exact` / `chunks_exact_mut` iterators. Its row says the frozen function extracts, so the text is not touched. A counting-loop form of an Aspis-only copy was not measured. |
| `SolanaDigest::digest_into` (program crate) | a trait implementation, emitted as a declaration | The deployed branch is the runtime's hash syscall; the tools see only the declaration. A runtime boundary, as in R1 (finding of the earlier probe; not re-examined in this pass). |


## 7. Boundaries relied on

Items of the two library crates that the final emissions reference (from
Charon's declaration lists of runs `TP-C40` and `TP-C41`, the same tree as
the release-style runs; full names in `translatability/verifier/data/boundaries-final.json`).
Whether they translate and elaborate is the other workers' table, not this
one; here they are what the verifier and the adapter stand on.

Verifier crate scope, aspis-core (58): `circle::secure_ood_circle_point_from_parameter`, `circle::{impl}::clone`, `circle::{impl}::eq`, `digest::Digest32::digest_into`, `field::P`, `field::wide_exact::{impl}::ONE`, `field::wide_exact::{impl}::ZERO`, `field::wide_exact::{impl}::add`, `field::wide_exact::{impl}::c0`, `field::wide_exact::{impl}::c1`, `field::wide_exact::{impl}::clone`, `field::wide_exact::{impl}::eq`, `field::wide_exact::{impl}::from_le_bytes`, `field::wide_exact::{impl}::from_limbs`, `field::wide_exact::{impl}::from_qm31`, `field::wide_exact::{impl}::mul`, `field::wide_exact::{impl}::mul_m31`, `field::wide_exact::{impl}::mul_qm31`, `field::wide_exact::{impl}::new`, `field::wide_exact::{impl}::sub`, `field::wide_exact::{impl}::to_le_bytes`, `field::wide_exact::{impl}::to_limbs`, `field::{impl}::ONE`, `field::{impl}::ZERO`, `field::{impl}::add`, `field::{impl}::clone`, `field::{impl}::double`, `field::{impl}::eq`, `field::{impl}::from_le_bytes`, `field::{impl}::inv`, `field::{impl}::mul`, `field::{impl}::mul_add`, `field::{impl}::mul_m31`, `field::{impl}::new`, `field::{impl}::reduce_u64`, `field::{impl}::square`, `field::{impl}::sub`, `r0::domain::{impl}::clone`, `r0::domain::{impl}::get`, `r0::domain::{impl}::new`, `r0::heap::filled`, `r0::merkle::C1_TAG`, `r0::merkle::C2_TAG`, `r0::scalar::{impl}::ONE`, `r0::scalar::{impl}::ZERO`, `r0::scalar::{impl}::add`, `r0::scalar::{impl}::from_m31`, `r0::scalar::{impl}::mul`, `r0::scalar::{impl}::neg`, `r0::scalar::{impl}::sub`, `r0::scalar::{impl}::try_inv`, `r0_transcript::queries_from_pairs`, `r0_transcript::{impl}::clone`, `state_only_hiding::state_only_selected_mask_value`, `state_only_prefix::r0::statement_points`, `state_only_prefix::r0::{impl}::clone`, `state_only_private_merkle::private_leaf_hash_with_digest`, `transcript::circle_fallback_point`.

Verifier crate scope, aspis-statement (3): `pool_v1::pair_forest_semantic_terminal::r0::{impl}::clone`, `pool_v1::pair_forest_semantic_terminal::r0::{impl}::public_bytes`, `pool_v1::pair_forest_semantic_terminal::r0::{impl}::terminal_qm31`.

Program crate scope, aspis-statement (59): `atomic_statement::decode_digest_canonical`, `pool_v1::format::POOL_V1_DIGEST_ENCODING_VERSION`, `pool_v1::format::POOL_V1_TREE_HASH_VERSION`, `pool_v1::format::POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT`, `pool_v1::format::POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY`, `pool_v1::format::validate_verifier_policy_v1`, `pool_v1::incremental_merkle::POOL_V1_TREE_STATE_MAGIC`, `pool_v1::incremental_merkle::POOL_V1_TREE_STATE_VERSION`, `pool_v1::pair_forest_accounts::POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING`, `pool_v1::pair_forest_accounts::POOL_V1_PAIR_FOREST_ALL_LANES_MASK`, `pool_v1::pair_forest_accounts::POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES`, `pool_v1::pair_forest_accounts::POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES`, `pool_v1::pair_forest_accounts::POOL_V1_PAIR_FOREST_LANE_COUNT`, `pool_v1::pair_forest_accounts::POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES`, `pool_v1::pair_forest_accounts::POOL_V1_PAIR_FOREST_LANE_MAGIC`, `pool_v1::pair_forest_accounts::POOL_V1_PAIR_FOREST_LANE_VERSION`, `pool_v1::pair_forest_accounts::POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES`, `pool_v1::pair_forest_accounts::decode_pool_v1_pair_forest_checkpoint_v1`, `pool_v1::pair_forest_accounts::decode_pool_v1_pair_forest_master_v1`, `pool_v1::pair_forest_accounts::pool_v1_pair_forest_output_lane_v1`, `pool_v1::pair_forest_accounts::{impl}::clone`, `pool_v1::pair_forest_terminal::POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES`, `pool_v1::pair_forest_terminal::POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC`, `pool_v1::pair_forest_terminal::POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES`, `pool_v1::pair_forest_terminal::POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC`, `pool_v1::pair_forest_terminal::POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES`, `pool_v1::pair_forest_terminal::POOL_V1_PAIR_FOREST_TERMINAL_VERSION`, `pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_request_v1`, `pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1`, `pool_v1::pair_forest_terminal::encode_pool_v1_pair_forest_terminal_result_v1`, `pool_v1::pair_forest_terminal::validate_pool_v1_pair_forest_terminal_result_against_statement_v1`, `pool_v1::pair_forest_terminal::validate_pool_v1_pair_forest_terminal_statement_v1`, `pool_v1::pair_forest_terminal::{impl}::clone`, `pool_v1::pair_forest_terminal::{impl}::common`, `pool_v1::pair_forest_terminal::{impl}::nullifier`, `pool_v1::pair_forest_terminal::{impl}::semantic_public`, `pool_v1::pair_forest_terminal::{impl}::transition_kind`, `pool_v1::pair_terminal::POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES`, `pool_v1::pair_terminal::decode_pool_v1_pair_verified_afterstate_v1`, `pool_v1::pair_terminal::encode_pool_v1_pair_verified_afterstate_v1`, `pool_v1::pair_terminal::{impl}::clone`, `pool_v1::pair_tree_profile::POOL_V1_PAIR_CAPACITY`, `pool_v1::pair_tree_profile::POOL_V1_PAIR_TREE_DEPTH`, `pool_v1::pair_tree_profile::{impl}::clone`, `pool_v1::payment_relation::{impl}::clone`, `pool_v1::verifier_dispatch::POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES`, `pool_v1::verifier_dispatch::POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC`, `pool_v1::verifier_registry::POOL_V1_VERIFIER_ENTRY_BYTES`, `pool_v1::verifier_registry::POOL_V1_VERIFIER_ENTRY_V2_BYTES`, `pool_v1::verifier_registry::POOL_V1_VERIFIER_REGISTRY_BYTES`, `pool_v1::verifier_registry::POOL_V1_VERIFIER_REGISTRY_V2_BYTES`, `pool_v1::verifier_registry::decode_verifier_registry_entry_v1`, `pool_v1::verifier_registry::decode_verifier_registry_entry_v2`, `pool_v1::verifier_registry::decode_verifier_registry_v1`, `pool_v1::verifier_registry::decode_verifier_registry_v2`, `pool_v1::verifier_registry::{impl}::clone`, `pool_v1::verifier_registry::{impl}::is_active_at`, `pool_v1::verifier_registry::{impl}::is_immutable`, `pool_v1::verifier_registry::{impl}::is_paused`.

Program crate scope, aspis-core (4): `digest::Digest32::digest_into`, `field::{impl}::ZERO`, `field::{impl}::clone`, `field::{impl}::eq`.

Program crate scope, verifier crate (9, boundaries of that scope; they are
rows of the verifier crate's own emission): `transport::{impl}::clone`, `transport::{impl}::eq`, `transport::{impl}::tag`, `verifier::PROOF_BYTES`, `verifier::candidate::fused::summed_format::PROOF_BYTES`, `verifier::candidate::fused::verify_summed_format_unobserved`, `verifier::candidate::parse_shape`, `verifier::checkpoint_size`, `verifier::{impl}::fmt`.

Solana SDK items the program crate scope references (account handles, the
clock sysvar, return data, the hash syscall, program errors) are runtime and
SDK boundaries, as in R1.

## 8. What was run, what was only read, and slips

Run on the host, every job through `fv_slot.sh` (8 GiB scope, never raised;
no job of this pass was killed for memory; the largest scope peak was
3,333,050,368 bytes, the final emission):

- the classification runs of section 2 (`TP-C01` to `TP-C04`, `TP-A01` to
  `TP-A04`, `TP-L01` to `TP-L05`);
- gates: `tp1-p0` (first version of patch 0; failed on compute, stopped by
  hand), `tp1-p0b` (second version; all but compute), `tp1-p0c` (stopped by
  hand: wrong program-test criterion in my script), `tp1-p0d` (third
  version: OK); `tp1-b1b` (first batch; failed through my errors, below),
  `tp1-f1` and `tp1-f2` (stopped by hand, tree superseded), `tp1-f3` (final
  tree: OK);
- the R1-feature builds of section 3 (`TP-R1-*`);
- emissions with their Lean compiles: `TP-A10` (first version of patch 1),
  `TP-E31` (first batch; then `TP-L31b`, `TP-L31c` with corrected adaptation
  rules), `TP-R-3` (`TP-A40*`), `TP-R-4` (`TP-A50*`), `TP-R-5` (`TP-A60*`),
  `TP-E70` (`TP-A70*`, the release-style emission of section 5);
- four construct probes, stand-alone crates under
  `translatability/verifier/mini/`: m01 (`TP-M01`), m02 (in `TP-B-b3`), m03
  (in `TP-R-3`), m04 (in `TP-R-4`);
- five compute runs with `fv_tp1_bisect.sh`: `b2` to `b6`.

Run on the development machine as a preflight only (local toolchain, not the
gate's; nothing here is evidence for the gate): the verifier crate's unit
tests with the deployed features and the client-configuration unit tests on
the candidate trees, and type-checks of every variant before it went to the
host. The program crate cannot be built natively on this machine (its
link-section names are ELF names).

Read and not run: the status table rows (`git show` of
`ONCHAIN-PATH-EXTRACTION-STATUS-20261111.md`); the client's close plan; the
call chain from `to_summed_format`; R1's emitted Lean for the rewritten
`claims` (`codex-cx-sound-int2-20261025/source-inputs/ClaimsUnrolledParentSource.lean`);
R1's claim-fission patch (in the main checkout's `docs/research` tree, sha256
b550885634d8abc0ffd19cce5bd89be2894b06fbcb62e1aa41f87ab137edeb9b), whose
helper texts the batch has line for line.

Not done: no Lean statement is proved about any emitted definition; the
equality of each Aspis variant with its pinned function ("equality owed") is
tested (unit tests, mutant campaign, replays), not proved; the rewritten
adapter functions have no differential oracle of their own beyond the program
crate's unit tests (run in both trees under two feature sets) and the
replays; the first tool pair was not rerun on the final tree; the R1-feature
build was not repeated on the third version of patch 0; the text of `claims`
could not be compared with R1's rewritten Rust file, which is no longer on
the host.

The host trees were restaged several times, in place; each restaging is a line
of `tp1/TREE-HISTORY.txt` on the host (copy in
`translatability/verifier/data/host-tree-history.txt`). `src-base2` was never
written.

Slips, all mine:

- Temporary files were written to and removed from the host's `/tmp` twice
  (an archive of summaries in the earlier probe; symbol listings early in
  this pass). Everything since is under `tp1/` in the workspace.
- Patch 0, first version: a `#[cfg]` on a feature the crate did not have
  (section 3). Found by its gate.
- The first batch (gate `tp1-b1b`): twelve unit-test call sites not updated
  for the changed signature, so the unit tests did not compile; a wrong
  `cargo test` filter, so the client-configuration step did not run; a
  helper inserted between another function's attributes and that function,
  found by reading the patch before the gate started; and a new version of
  the gate script copied to the host while the gate was running it, which
  ended that run with a shell error after the mutant runs. The two mutant
  comparisons of that run were made by hand on the files it left (observed
  run identical to the base, sha256 e3659a53d3b4e308711668d82715cd981e8d3bdc7ba859c9ff3bdaa1e3c9e2b9; deployed run: all mark counts
  0, verdicts identical, sha256 a050df4712fb841d90841914f8d528fa435da5956e2ba92da29651e078c81981); it has no worst-case run. Scripts
  are now changed only when none of my jobs is running.
- Gates `tp1-p0c` and `tp1-f1`: my gate script failed the gate whenever a
  program-crate test failed, and 25 fail in the base tree itself under the
  deployed features. Found when both trees showed the same result line; the
  script now compares the outcomes test by test (`fv_tp1_gate2.sh`).
- Reports to the lead named patch hashes that were later superseded twice;
  the superseded patches are kept with a note each.

Host scripts added by this pass (`evidence/future-version-20261111/host/`):
`fv_tp1_gate2.sh` with `fv_tp1_gate2_inner.sh` (the gate, one scope; the two
gates that count ran with it), `fv_tp1_emit1.sh` with
`fv_tp1_emit1_inner.sh` (translation, scan and Lean, one scope),
`fv_tp1_bisect.sh` with `fv_tp1_bisect_inner.sh` (compute by variant),
`fv_tp1_round.sh` (probe, compute and emission in one scope),
`fv_tp1_lean1.sh` (Lean on an existing emission), `fv_tp1_mini.sh` (a
construct probe), `fv_tp1_symcmp.sh` and `fv_tp1_symcmp2.sh` (function sizes
of two ELFs), `fv_tp1_r1cmp.sh` (R1-feature build against the PIN2 ELF),
`fv_tp1_classify.sh` and `fv_tp1_p0.sh` (the first runs). Superseded and kept
as the record of the runs made with them: `fv_tp1_gate.sh` (gate `tp1-p0b`),
`fv_tp1_gate1.sh` with `fv_tp1_gate1_inner.sh` (wrong program-test
criterion), `fv_tp1_batch.sh` (never completed).

What the lead's scripts need if the patches are adopted. The shared gate
`fv_sampler_gate.sh` would fail on the final tree for two reasons that are
about feature names and not about behaviour: (a) its native builds name
`aspis-core/future-lazy-horner`, which now compiles the pinned
`semantic_value`; they must name the verifier crate's `future-lazy-horner`
(`aspis-r1-cost-probe/future-lazy-horner` from the tools crate); (b) the
mutant tool counts observer marks, and the one-transaction functions carry
the observer only with the verifier feature `phase-observer`, so the campaign
needs `aspis-r1-cost-probe/phase-observer` to reproduce the base's marks, and
a second run without it is the one that executes the functions the deployed
program executes. Every Charon run on the verifier crate must likewise name
`future-lazy-horner`.
