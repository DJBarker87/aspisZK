# Lead cone repin after S4 adoption — 22 October 2026

Source target: `25866ec331cc7ce27dd9956609c11d32fa8fa58a` on
`codex/cx-lead-repin-20261022`, containing adoption
`29cbab431742f7e899870595167efa193a379f0a`. Old frozen source:
`b2727acd3abf79315d18b754a260f58f4b1c6326`.
Authority: [S4 decision](../../design/S4-ADOPTION-DECISION-20261022.md) and
[C3 11:50 addendum](../../design/C3-BIN-20261021.md).

This is a source/text identity overlay, not a fresh source extraction or
release proof. No shipped file, existing Lean module, session-A candidate,
S1–S6/S9 module or security contract is edited. No Lean process is started,
so neither the night-window exception nor the concurrent env-J job is used.
No proof, runtime, Kani, Rust or SBF regression is repeated.

## Pin table

The next section supplies full changed-file and artifact pins. Exact full
per-item old/new hashes, source line ranges, receipt paths and manifest
hashes are in [pin-checks.json](pin-checks.json),
[function-checks.json](function-checks.json),
[model-pins.json](model-pins.json) and [artifact-pins.json](artifact-pins.json).
An unchanged item is re-recorded at the target revision with the same hash;
a historical aggregate manifest is never rewritten to claim a new run.

| Cone | Artefact | Old pin | New pin or HISTORICAL | Action |
|---|---|---|---|---|
| S7 | `repin-s7` LLBC declaration slices; `s7-kani` literal items; `s7-join/source-bindings.json` | Frozen verifier/candidate/domain/field texts, individually pinned in receipts | Same exact texts at target; `extraction-text.json` and item hashes | Retain local basis/inverse/accumulator and reference results; re-record source bodies only. |
| S7 | `s7-kani` / `s7-kani3` extraction input aggregate, linked `fast_dots`, `fast_pairing`, `weights` files | `32d90c30…`, `5a84d748…`, `30e8f10f…` | HISTORICAL aggregate; new file hashes below | Copied `weights::field` is unchanged; this cut does not copy `powers`. Opaque dot dependencies and real caller composition stay open. |
| S8 | `EbyKDot::{new,push,finish}`, `checked_q` | Exact old function bytes | Same bodies; full hashes below | Retain body pins, but do not infer unchanged transitive semantics. |
| S8/S5 | `canonical::Q::from_limbs` reached by `checked_q` → `EbyKDot::push` | `be073dde…` body; `5a84d748…` file | HISTORICAL old constructor/source binding; new body `5c935940…` | Four-limb predicate/Option correspondence and extraction/caller rebind required; S5 owner, S8 consumer. |
| S8 | `repin-s8` declaration slices; `s8-kani{,2}`/`s8-join` finish/scan/reference modules | Pinned verifier/compact/field and owned finish extraction | Same exact local bodies/model pins | Retain `S8Kani2FinishReferenceJoin`, `S8JoinCompactTotal.check_values_total`, `S8JoinRawCongruence.mutable_finish_eq`, `S8P6ReturnedFinish.{mutable_certificate,finish_certificate,stage_observation}` at their existing P6/reference scope. Their final dot is a field reference, not an EbyKDot source theorem. |
| Multiproof | `source-pins.json`, `source-cuts.json`, physical/P6/batch extraction and gates | Pinned multiproof/candidate/compact/field source cuts | Unchanged cut hashes; retained extraction-manifest hashes in pin-checks | Retain `MultiproofConeP6Frozen2Stage.{function_certificates,sourceBatch_eq,both_batches}`; actual S2/S10 caller binding remains open. |
| Parser/compact | Multiproof parser/header/codec/strict scanner plus earlier parser extraction packets | Exact production item or historical candidate pin in each receipt | Current items unchanged; older alternative candidates remain HISTORICAL wherever hashes differ | Retain `MultiproofConeParserTotal.{rows_join,parse_total,accepted_parse}` reference scope. No production-parser adoption inferred. |
| Checkpoint ABI 1–5 | Writer/Reader/resume, codec, field-section, std/allocator and CFG cut pins | `verifier.rs` `8c872d42…`; field and retained emitted bodies | Same bodies at target | Retain local contracts, emitted results and `OraclePortCkptAbi5Stage.stage_observation`; preparation/query/pending-finish provenance remains separate. |
| ckpt-bytes1 (`ckpt-bytes-20261021`) | `source-pins.json`, sparse/raw decoder bodies | Retained verifier/Stage2 resume/field/codec pins | Same body pins | Retain raw-byte bridge only at recorded source/P6 boundary. |
| ckpt-bytes2 | `source-check.json`, production reader and K-section Kani | Verifier/field/wide_exact/reader-source pins | Same body pins | Retain section/cursor/canonicality results; no powers or fast_pairing body in this cut. |
| ckpt-bytes3 | Reader + section extraction and operation gates | Retained production reader/sections and sparse byte reference | Same current cuts; older draft harness pins stay historical | Retain section results at actual operation contracts. |
| ckpt-bytes4 | Fixed-width, std reader, saved-field/reference/weights joins | Retained Stage2 reader and model/source snapshots | Same current cuts/model hashes | No re-proof caused by S4 adoption; field-value provenance is still a caller obligation. |
| ckpt-bytes5 | Writer/resume schedule, whole stage and decision replacement | `source-schedule.json`, `CheckpointBytes5Join`/`Decision` receipts | Same writer/resume and model source | Retain `success_conditioned_checkpoint_stage_join`, `decision_success_join`; `S1S7S8StateProvenance` must be supplied for adopted powers/dot callers. |
| S10 | Frozen source census, MIR/LLBC instance ownership and native diagnostics, passes 1–5 | 488-file baseline and old compiler declaration/closure IDs | HISTORICAL aggregate; current census and ownership overlay supplied | Retain source-independent inventory/ordering mathematics. Re-extract changed declaration/instance edges before claiming adopted completeness. |
| S10 | Verifier ELF graphs, call instructions, symbol/inline maps and default/devnet CFG certificates | `dfc2a91a…` / `fb2fc048…` (and historical linked/debug ELFs) | HISTORICAL; adopted `40dc7574…` / `12cb0bc2…` | Old machine addresses, instruction counts, code identity and debug comparison results do not transfer. No new instance census claimed. |
| S10/Pool | Retained Pool ELF | `121f3e29…` | Same retained artifact pin | Reuse Pool artifact evidence only; changed verifier CPI target/proof binding is separate. |
| frozen2 headline/cone joins | `OraclePortFrozen2Cones`, `OraclePortFrozen2Join`, `OraclePortFrozen2Headline`, `OraclePortHeadlineFrozen2PerAttempt` and associated model modules | Current retained theorem/source pins | Same exact model/theorem statements; pinned at target in model-pins | Retain conditional `acceptedRunJoin_of_total_cones` and headline `final_soundness`. No concrete adopted `PerConeJoins`, S10 source tree, source/model identities or runtime binding supplied. Zero premise removal. |

## Full changed pins

- `crates/aspis-r1-cost-probe/src/fast_dots.rs`: old `32d90c30e36dea620da0619bfdd9bd7fce3973fb22a3d8c30deb42a79a0ccd61`; new `53fa714e84ded64b844061f4d1b66ad20ee1ba48c3873a73970f80ede8a0b602`.

- `crates/aspis-r1-cost-probe/src/fast_pairing.rs`: old `5a84d748e3ac495a664e6b476c0b91a4bfa47408e76661a2834726d40ff28ea0`; new `2cb96261cecfd766b5e1b45a585b74c5f59c20c6be4f41e806239e2786ca7313`.

- `crates/aspis-r1-cost-probe/src/weights.rs`: old `30e8f10fa7f0adfe2101bb5df8bdfe0876ee70b35349ab886ab4dc30a0d16cca`; new `28b558ffa9f5b004188c7f50b1597fe681186f54fb4d52a3bd125df4f2481137`.

Changed function bodies (signature through final brace, whitespace significant):

- `fast_dots.rs::four_dots` occurrence 1: `4c4407dbebaa2726c998b32245275357a23517a3941098103f92ab3a69a537cd` → `70892029d20e9133b92c333327f6ea3d9d751ade20643c365e0335624099c547` (HISTORICAL).

- `fast_dots.rs::four_dots_one` occurrence 1: `absent` → `493685b837b3dbba8908cbbb1e5a5bf01eeb9bf88571d2ce9bfc403197f36eb7` (new).

- `fast_pairing.rs::checked_q` occurrence 1: `d9f65f3333dfdb7ec651d8674f2f9e4ec55a03f5921e034b1c6fb79518b1731f` → `d9f65f3333dfdb7ec651d8674f2f9e4ec55a03f5921e034b1c6fb79518b1731f` (unchanged).

- `fast_pairing.rs::finish` occurrence 2: `37b2b00d84bd795b342871bf9f3966071678a6f08843a073636a5595bdf37aa8` → `37b2b00d84bd795b342871bf9f3966071678a6f08843a073636a5595bdf37aa8` (unchanged).

- `fast_pairing.rs::from_limbs` occurrence 1: `be073dde8b2176322c86846e13d0c1d246f96d0b5b0ae4a56245ca98218c668c` → `5c9359405f0fadf3d9d4fcdfa68258e263205534028f16ddcad06848b103b1c6` (HISTORICAL).

- `fast_pairing.rs::new` occurrence 2: `d1e03b1d0cdaf5c02996c2ba706d70e4d1364a75fe27814a638f856fb9b98e00` → `d1e03b1d0cdaf5c02996c2ba706d70e4d1364a75fe27814a638f856fb9b98e00` (unchanged).

- `fast_pairing.rs::push` occurrence 2: `250f443031119bbe9d662d4c7588d4fb8ca10b388855cf89eda73e1325e1aae3` → `250f443031119bbe9d662d4c7588d4fb8ca10b388855cf89eda73e1325e1aae3` (unchanged).

- `weights.rs::powers` occurrence 1: `3919d83b539f8819c40251a84625b582ac88338fed2fa14b18951a69c0e1d018` → `79c059dd574e3b0dac53ca40f02072d473466dc58ab231f23636f94285b12a22` (HISTORICAL).

Adopted artifact pins, reused from the approved retained identity receipt (no new ELF build/hash measurement):

- default: `40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0`.

- devnet: `12cb0bc2f8ff3993643638080a3786fdcd941910e5e4dd65ae2937a99290c28f`.

- pool: `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.

## Exact invalidation and remaining proof size

**S8:** the only changed fast_pairing function is
`canonical::Q::from_limbs`. Its implementation replaces
`x.iter().all(|&v| v<P)` by destructuring `[a,b,c,d]` and four short-circuited
comparisons. `EbyKDot` and `checked_q` match exactly, including MAX_TERMS,
pre-check error, field operations, count update and finish bytes. Nevertheless,
`checked_q` calls that changed constructor, so a whole-backend claim cannot
be re-pinned merely from the three EbyKDot hashes.

The affected certificates are the **whole-file source/extraction bindings**
listing old fast_pairing: `repin-s7/{charon-input,aeneas-input}.json`,
`repin-s8/extraction-s8-stage2-01/{charon-input,aeneas-input}.json`,
`s7-kani/source-binding.json`, `s7-kani3/source-preflight.json`, and the S10
native/frozen compiler/ELF instance certificates. Each matching receipt is
listed by full path in pin-checks/artifact-pins. Their bodies may be retained
as explicit opaque cuts; their aggregate current-source assertion is
historical. Both repin extractions declare `crate::fast_pairing` opaque;
they do not contain a proof of the changed constructor to invalidate.
No inspected S8 theorem proves EbyKDot implementation semantics: the final
dot in `S8P6ReturnedFinish.finish` is explicitly the field reference.
Thus no completed local scan/residue/finish theorem is revoked; the missing
backend-source binding remains missing against the newly pinned constructor.

Exact next proof: one total four-U32 constructor Result/Option lemma,
including any limb ≥P and arbitrary U32 inputs, showing exactly the same
canonical Q or rejection without state/oracle effects. Then one checked_q
binding and one EbyKDot::push composition (preserve pre-count rejection,
poststate and count); EbyEDot uses Q::from_wide directly and does not reach the changed constructor. Size:
one four-coordinate Boolean case/array lemma and two caller adapters, not
finite-field enumeration, recurrence normalization, or a new dot arithmetic
proof. S5/session A owns the constructor; lead S8 consumes its named result.
This is required work, not a newly proved theorem in this packet.

**S7/S9 weights:** `weights::powers` changes from an N-call from_fn closure
to an initialized array/indexed loop with an early return after the last
write. N=0 returns the empty initialized array; for N>0 only N−1 products
are evaluated. The old final unused multiplication must not be silently
identified with the new execution. `kpowers`, `field`, `Weights::{new,pair}`
and Libra formulas match byte-for-byte; their bodies alone do not certify
the changed powers dependency. The S7 literal cut copies **only `field`**
from weights, and its extraction declares weights opaque. Existing S7
basis/geometry/owned-accumulator proofs therefore retain their exact local
scope. In particular `S7JoinAccumulation.total_exact` and
`S7P6AccumulatorIterations.total` do not assert the missing original
preparation/query binding or prove powers.

The old full weights source-manifest/extraction pin is historical. The
old S3/S9 source instance/caller binding for N=4, Prepared kappa N=7 and
scratch/settlement gamma N=29 must consume session A's adopted
`early_powers_total_exact` generic indexed-body result, with exact extraction
identity, canonical operands and library interpretation. Size: one already
owned generic loop induction, its N=0/N>0 exits, and three size
specializations (4,7,29); then the reached Prepared/Weights/caller adapters.
No exhaustive 29-cell evaluation is required. No S9 model identity theorem
is reinterpreted as a source execution theorem. `kpowers<4>` and the Libra
`terms` from_fn remain separate **unchanged but still open** boundaries.
Do not re-prove S4 or edit its modules/candidates. The lead's outstanding
work is integration with those Session A results, S7 query/opening and S8
returned-state provenance, not a duplicate powers or four-dot proof.

**Checkpoint/parser/multiproof/frozen2:** the body pins of their actual
writer/reader/resume/parser/Merkle helpers are unchanged by adoption.
`CheckpointBytes5Join.success_conditioned_checkpoint_stage_join` and
`CheckpointBytes5Decision.decision_success_join` retain the named
`S1S7S8StateProvenance` and `S2S10CallerBinding` obligations. Rebinding those
to the adopted Prepared/weights/dot outputs remains necessary, but the
byte-codec and six-read stage lemmas need no adoption re-proof. Likewise the
P6 multiproof stage is not a proof of the enclosing new ELF caller. The
frozen2 composition and per-attempt headline are source-parametric: their
statements remain valid; no actual source instance is supplied by re-pinning.

## S10 ownership and aggregate census

[ownership.json](ownership.json) recomputes all 160 old generic MIR records
in the adopted files and adds the new `four_dots_one` source declaration.
It preserves one owner per record: S4 for both dot functions, S5 for the
canonical constructor, S8 for EbyKDot, S3 for generic powers. Powers is shared
by S1/S3/S9 and reached S7 callers, but shared consumers are not duplicate
ownership. Pass-4 `owner-lowering.json` confirms powers' `.owned .s3`
assignment. Old from_fn/iterator-predicate closure records are removed from
the proposed adopted inventory; constant/span/instance IDs must be
regenerated, not guessed. The new helper has no invented compiler ID.
All nonchanged methods retain their semantic owners; shifted line spans
and any default/devnet deployed-instance IDs remain historical.

The full old 488-file census has 472 exact matches and 16 mismatches. Three
are the adopted files; the other thirteen are independently listed in
source-census.json (prover/simulator/wire, statement helpers and checkpoint
tests). They are not falsely attributed to this S4 adoption or silently
accepted as a coherent new source manifest. Earlier parser experiments and
intermediate tool/Lean snapshots also produce historical pin mismatches;
pin-checks.json preserves each old hash and contributing receipt. A mismatch
is never converted to a passing final theorem audit. Whole-source census,
final reachable instance/inline correspondence, source Calls tree,
source/model ordering and owner acceptance remain incomplete.

The old default/devnet ELF graph, address/callx/relocation and native/SBF
correspondence certificates are historical. Re-recording the adopted ELF
hashes is **not** regeneration of those certificates. Pool's unchanged hash
retains its own artifact evidence, not an unchanged verifier callee proof.
S10's `covered`, model ordering, std-boundary and strict-order results remain
model facts; neither previous incomplete gates nor this overlay discharge
adopted-source completeness. The next compiler deliverable is a scoped new
changed-declaration/instance census, then caller/source-tree composition and
one coherent release replay after the owners' proofs are ready.

## Verification and trust boundary

Stage 1 pins 71 evidence scopes and 3,458 JSON inputs; exact file/item
checks include prior attempts, with every resolvable tracked pin retained.
Stage 2 checks all 126 retained S7/S8 declaration-text slices: every one
occurs exactly as retained in current source (not necessarily uniquely).
Model-pins records 345 current lead/model source files and matching retained
receipt references. These are hash/text observations, not compiled results.
The repeated-signature function slicer was corrected to slice at the lexical
match offset, so ExEDot methods are not mistaken for EbyKDot methods.

Reproduce without Lean:

```
python3 -B docs/research/100bit-spend-path-20261013/evidence/lead-repin-20261022/impact.py --check
```

The validation receipt records command, exit, wall, RSS, swaps and source
revision. No new theorem exists, so a new `#print axioms` run is inapplicable;
retained standard-axiom proof receipts are reused, never reported as a
coherent new release proof. No assumptions are discharged, added or weakened.
The remaining source/implementation joins are proof obligations, not new
cryptographic assumptions. **Target not yet established.**

Final focused validation: [validation.json](validation.json), exit 0,
11 checks, wall 11.137223 seconds, peak RSS 250,953,728 bytes, swaps 0.
Receipt source revision is `96b1b1dac52c076e73d984f09fd5cf3fa09ab974`;
the exact audit scripts, including the final linked-artifact reference
extension, are pinned by SHA-256. The six old deployed/linked artifact hashes
have 32 explicit retained references; default/devnet linked pins are retained
historically, with no invented adopted linked ELF hash. Final scope inspection
also confirms the new validation files are confined to this evidence directory.
