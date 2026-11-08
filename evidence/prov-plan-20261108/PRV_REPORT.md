# PRV: sizing and plan for the (bk) re-extraction campaign

Target not yet established. This is a read-only planning analysis. It changes no row, trust item, ledger, proof or shipped source, and it ran no Charon, Aeneas, Lean or Kani process. Every number below comes from committed evidence on `research` at f7ccfbace7a, with the ledger27 gate (`evidence/ledger27-20261111`) as the basis. The machine-readable partition is `PRV_PARTITION.json` and the scripts that produced it are in `PRV_scripts/`. They were run without the `PRV_` prefix, from `evidence/` with a scratch directory argument, in this order: live, decls, scanall, modmap, emods, emods2, classify, final. emods2 and classify import decls and defseg.

## 1. What was measured, and how

The NMH_/NML_ impact figure (561 CLOSED rows on ledger24, 566 on ledger27 by the same method) intersects lexical declaration names from all 336 blobs with every CLOSED root's reachable-constant list. It treats every historical copy of a module as if it were compiled, so it is an upper bound by construction. This analysis replaces the name match with three facts the gate itself records.

First, the gate has exactly one compiled source per module name. `NNK_LOADED_scan.jsonl` gives, for each of the 18,581 loaded modules, the olean's import list and declaration count. A committed file can be the compiled source of module M only if its path names M and its import set equals the olean's. That filter alone shows that 50 of the 336 blobs are superseded versions that were never compiled into the gate.

Second, the inventory was rebuilt from the gate's side rather than from the blob list. All 61,350 distinct tracked `.lean` blobs were indexed. 364 gate modules have an import-matching committed source carrying an Aeneas header or Rust-item annotations. Six more modules were compiled from renamed files, which were found by import equality plus namespace. For example, `AspisR1SelectedMaskProbe.Funs` and `.Types` come from `evidence/replay-dry5-20261026/RPz4_SelectedMaskFuns.lean` and `RPz4_SelectedMaskTypes.lean`. That makes 370 emitted modules in the gate.

Third, row reliance uses the ledger's canonical owners. ledger27 has 587 CLOSED rows with 1,087 distinct `root_owners` (TX1:059 and TX2:040 remain rootless). A row relies on module M if one of its roots reaches a constant owned by M. Ownership means the name is declared in every import-matching candidate of M. Private names carry their module in `_private.M.0`. Auxiliary names such as matchers, equation lemmas, constructors and projections resolve to the longest declared prefix.

Receipt status per compiled candidate counts as receipted if any of these holds:
- NKT recorded it as `HASH_LINKED_PIN_RECEIPT`;
- NMH or NML reproduced it;
- its sha256 appears in a `*PINS.json`, `*-pins.json` or `*EXTRACTION_PINS*.json` file.

Lean compile receipts (`_Lnnn/receipt.json`) and inventory or export JSON do not count.

Coverage asks, for each definition a CLOSED root actually reaches, whether a fresh receipted emission from the frozen revision already contains the same Rust item. It uses the Aeneas doc-comment segments of the 223 emitted files whose pins name `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387` (924 Rust symbols). Text is compared with comments and whitespace stripped and crate names normalized.

## 2. Findings

### PRV-F1: the accurate impact is 532 to 538 CLOSED rows, not 561 to 566

Rows that rely on at least one group (c) module: **532 of 587**. Adding the reference-crate modules whose source is not hash-linked (group b2/b3) gives **538**. The 19 modules whose live version is ambiguous between a receipted emission and its retained copy (a_pending) add no further rows. 553 rows touch at least one non-receipted emitted module of any kind, including the trivially-identical ones.

The reduction from 566 is real but small. The impact is broad because a few hub modules sit under most of the spend path. Examples (rows in parentheses):
- `RPz7_FIo_NativeTypes` (182), `RPz7_FIo_NativeFuns` (169) and `RPz7_FIo_NativeExternal` (114)
- `Stage2ContinuationTypes` (163)
- `AspisR1CurrentWide.Funs` (113)
- the QRaw cluster: `FIo_QRawTypes`, `FIo_QRawFuns` and `AspisR1CanonicalQRawUnified.*` (111 each)
- `AdapterRwTypes` (99)
- `AspisR1TerminalDecoder.Types` (93) and `.Funs` (82)
- the neg_isolated reference cluster: `NFS_AccumPart00` (92), `NEV_AccumulateRaw.Types` (88) and `NEI_PushRaw.*` (81)

A row is clean only when every module under it is fixed. 309 affected rows depend on 1 to 4 problem modules and 16 depend on more than 50. If problem modules are fixed in descending order of row count, 10 modules free 49 rows, 30 free 289, 50 free 332, 100 free 450, and all 160 free 538. A partial campaign therefore buys little. The campaign has to cover all 160 problem modules (c, b2/b3 and a_pending) before the release line can change.

The conservative figure was not wrong as an upper bound. It is replaced here by a gate-anchored count. The difference comes from superseded versions, unreached modules, and names that only stale copies declare.

### PRV-F2: the 336 list is incomplete as a release inventory

The 336 blobs come from NKT's file-based superset. The gate's own module table shows 17 relied, non-receipted modules whose compiled source lies outside the 336. Six of them, including `AspisR1SelectedMaskProbe.Funs/.Types` (renamed RPz4 sources) and `AspisR1QueryGeometryActual.Funs/.Types`, are absent from NKT's 428-blob extraction inventory altogether. For seven module names that do appear in the 336, the compiled version is a different committed file:
- `AspisR1SelectedMaskProbe.Funs/.Types`
- `AspisR1WithdrawalValidation.Funs`
- `NFG_InverseRef.Funs`
- `NEV_DotResult`
- `NFY_Part056`
- `NFY_Part057`

Two of those, `AspisR1WithdrawalValidation.Funs` and `NFG_InverseRef.Funs`, are hash-linked receipted. The release obligation should be stated over gate modules, not over a blob list. `PRV_PARTITION.json` does this.

### PRV-F3: partition

Blob-level (the 336):

| group | blobs | detail |
|---|---:|---|
| (a) covered | 65 | 13 reproduced by NMH/NML; 26 whose module's reached definitions are text-identical to a fresh frozen receipted emission; 26 a_pending (module also has a receipted candidate) |
| (b) reference crates | 17 | 3 source committed and hash-linked (b1); 1 committed but not linked (b2); 13 source not found by a bounded search (b3) |
| (c) frozen-source translations | 138 | 40 c1 (fresh extraction already exists, equality needed); 90 c2 (new extraction and equality); 8 c0 (no annotated definition reached; hand-transformed copies) |
| (d) not relied on | 116 | 50 superseded versions not compiled into the gate; 63 in modules no CLOSED root reaches; 3 in modules with no emitted candidate |

Module-level (370 emitted gate modules, the unit the campaign works on):

| group | modules |
|---|---:|
| receipted or reproduced (live version) | 69 |
| (a) a_identical | 20 |
| (a) a_pending | 19 |
| (b) b1 / b2 / b3 | 3 / 1 / 16 |
| (c) c1 / c2 / c0 | 39 / 75 / 10 |
| (d) not reached by any CLOSED root | 118 |

The (c) modules split as 52 transformed copies (RPu_FIq_*, RPv_*, RPz7_*, S1*, Port23 and similar), 43 probe or cut crates (`aspis_r1_stage2_adopted_caller`, `aspis_r1_mask_extraction_probe` and others) and 27 frozen-crate emissions. The remaining 2 are frozen-crate modules carrying a Ref name. In 15 of the (c) modules some uncovered definitions belong to a cut crate with no frozen counterpart: `WAdm_model`, `values_owned_reference`, `check_values_owned`, `copy_chunk`, `encode_digest_canonical` and the QRaw `canonical::raw` items. For these, a frozen re-extraction cannot reproduce the committed definition. They need either the cut crate's committed source (handled like group b) or a re-route of the parent bridge to the frozen function.

### PRV-F4: size of group (c)

Reached definitions in the 124 (c) modules:
- c1: 238 definitions, of which 146 are text-identical to an existing fresh frozen emission and 92 differ.
- c2: 765 definitions, of which 173 are identical, 119 are covered but differ, and 473 are not yet in any fresh frozen emission.
- c0: 10 modules with no annotated definition reached. These are hand-transformed copies or external models, mapped by hand.

Extraction runs: the 473 uncovered definitions fall into 27 frozen source modules. The largest are:

| frozen module | defs |
|---|---:|
| field | 82 |
| pool_v1::payment_relation | 56 |
| state_only_poseidon | 53 |
| pool_v1::pair_forest_semantic_terminal | 43 |
| verifier | 33 |
| pool_v1::pair_forest_copy_terminal | 26 |

The cut-crate items fall into about 10 more configurations. Group b needs about 8 reference-crate configurations. Allowing about 1.3 Aeneas selections per frozen module for opacity splits gives 35 frozen selections, plus 10 cut and 8 reference selections, which is about **53 runs**. With a 25% retry allowance the ceiling is **65 scopes**. At today's 2 to 3 minutes each that is 2.2 to 3.3 scope-hours, under 1 hour of wall time at 6 concurrent scopes. One Charon LLBC per crate can be reused across selections (NML showed LLBC reuse works).

Equality proofs (estimate; calibrated in section 3):

| class | definitions | method |
|---|---:|---|
| rfl-trivial: identical text after normalization | about 636 (146 + 173 + about 317 expected among the 473 uncovered) | generated `rfl` / unfold-chain theorems |
| differing text | about 367 (92 + 119 + about 156) | |
| of which nominal (namespace, explicit opaque-call parameters, imports, discriminant metadata) | about 320 | one generic transport tactic per module pair |
| of which semantic or source-shape | about 25 to 45 | hand proofs, possibly with a caller-domain lemma |

### PRV-F5: group (b)

Of the 20 reference-crate modules, only 3 have a committed, hash-linked reference source (`FIn_ExtractFuns`, `NHI_FilledTypes`, `NHI_FilledExtracted`). One (`NEI_PushRaw.Funs`) has a committed source in its job directory that is not linked to the emission. For 16, a bounded search found no committed source: at most 400 `.rs` files per job directory were checked for the reached function names. The search may have missed sources stored elsewhere, so b3 means not located, not proven absent.

The b3 set includes the neg_isolated hub (`NFS_AccumPart00`, `NEV_AccumulateRaw.Types`, `NEI_PushRaw.Types`, reaching 81 to 92 rows each) and the Multiproof*Ref family. If a reference source cannot be located, the honest options are to reconstruct it and re-run its Kani contract, or to re-route the bridge to a frozen extraction. Either is a scope decision for the lead.

### PRV-F6: calibration

NML_DIFFS_CLASSIFIED covers the 17 historical-versus-fresh differences, 216 compared definitions in all. 145 (67%) are identical. Of the 71 that differ, 16 are the two SEMANTIC blobs (`NFG_InverseRef` L031/L032, eight definitions each, M31.add on non-canonical U32 inputs). The other 55 are nominal or unclassified: imported carriers, explicit opaque-call parameters, selected declaration sets. NND's `require_zero` (index loop in the historical 81521c77 candidate versus suffix loop in the frozen source) is the source-shape case: a real loop-equivalence proof, not a renaming. The estimates above apply 67% identical to the uncovered definitions and about 7 to 12% semantic or source-shape to the differing ones.

## 3. Recommended equality method

State every equality against the gate's compiled constant, not against a source file. A generated module imports the gate export (`NNK_COMBINED_IMPORT`) and the fresh frozen emission. The fresh emission is deterministically renamed into a `PRVFresh_<M>` namespace and compiled against the committed Types module whenever the Types text is identical, so the two Funs constants share types. The module then proves `PRVFresh_M.f = M.f` for each reached definition, in callee-first order. It tries `rfl` first, then unfolding with the callee equalities, then a per-module nominal transport, then a hand proof.

This approach has four advantages:
- It never needs to know which historical file produced a module, which also settles the 19 a_pending modules.
- It never rebuilds the thousands of downstream oleans.
- It leaves every CLOSED root statement untouched.
- It gives each definition a theorem whose `#print axioms` can be audited.

Re-pointing a hub module to the fresh emission and replaying its dependents is the alternative. AGENTS resource policy argues against it except as the final release replay.

Where a definition differs semantically (the M31.add class), the theorem is a domain-restricted equality, and the job must show from the CLOSED callers' recorded domains that every use stays inside that domain. NML_DiffArithmetic.lean is the template. A definition with no equality theorem keeps its rows conditional for the release claim, per the (bk) addendum.

## 4. Campaign size

| phase | jobs | model | host scopes | wall time (6 slots) | tokens (estimate) |
|---|---:|---|---:|---|---:|
| P0 tooling, generator and 3-module pilot | 1 | sol | 10 to 15 | 0.5 day | 1.0M |
| P1 fresh frozen extractions | 2 | terra | 55 to 65 | 0.5 day | 0.8M |
| P2 generated equality modules (rfl / unfold) | 4 | terra | 90 to 130 | 1 day | 2.4M |
| P3 differing definitions (nominal transports, semantic cases) | 4 | sol | 60 to 100 | 2 to 3 days | 4.0M |
| P4 reference lane (b2/b3, cut crates) | 2 | terra, escalate b3 | 20 to 40 | 1 day, parallel | 1.0M |
| P5 a lane (a_identical regeneration, a_pending constant equality) | 1 | terra | 30 to 45 | 0.5 day, parallel | 0.4M |
| P6 composition, axioms audit, ledger provenance line | 1 | terra | 8 to 12 | 0.5 day | 0.6M |
| **total** | **15** | 10 terra, 5 sol | **about 280 to 400** | **about 4 to 5 days on the critical path** | **about 10M** |

The scope counts follow from the module and definition counts above. The wall-time and token figures are planning estimates based on recent jobs (NMH/NML used 30 to 40 extraction scopes each; NNK used 60 Lean scopes; NMM/NMO used about 1M tokens each). None of them is a measurement of this campaign. Scope caps follow the NNK pattern: extraction scopes MemoryHigh 3G, MemoryMax 4G (NMH peak RSS was 0.93 GB); Lean scopes MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0. All scopes are admitted against the 55 GiB reservation, with at most 6 concurrent.

## 5. Limits of this analysis

- Declarations are lexical. Names produced by macros or unusual syntax may be missed. The module-level row count is robust to this, because every reached module has many declared names.
- Receipt detection is by hash presence in pins-named JSON. A pins file that lists an input hash rather than an output hash would be over-credited, which can only lower the count of unreceipted modules.
- For the 19 a_pending modules the live version is ambiguous. P5 settles each by constant-level equality to the receipted emission. Until then they stay in the conditional set, but they add no rows beyond (c).
- Coverage identity uses normalized text, not elaboration. P2's `rfl` results are the ground truth and will move some definitions between classes.
- The b3 search was bounded, as described in PRV-F5.
- TX1:059 and TX2:040 have no named root (NKT-F3), so their reliance is unassessed. They are not counted in either figure.
- Fresh receipted extractions merged after f7ccfbace7a are not included. They will shrink group c, so P0 recomputes the partition at its own base revision.

## 6. Status

Extraction provenance remains a release blocker under (bk). Accurate impact: 532 CLOSED rows rely on unreceipted frozen-source translations, and 538 including reference crates without a hash-linked source. Campaign: 15 jobs, about 280 to 400 scopes, about 4 to 5 days, about 10M tokens. No row is reopened and no trust row changes. Target not yet established.
