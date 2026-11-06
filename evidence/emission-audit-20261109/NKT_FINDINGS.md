# NKT emission-fidelity findings

Target not yet established. Audit only: no row, ledger, trust item, proof, Rust source or ELF changed. **This is not a complete universal fidelity certification.** The pattern scan and root-impact triage are complete for the enumerated tracked superset; exact extraction provenance remains incomplete as described below.

## Confirmed defect: NKT-F1

Frozen `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`, `crates/aspis-r1-cost-probe/src/candidate.rs::batch_tree`:

| Rust exit | Frozen line | Raw NJS Lean lines | Emitted effect |
|---|---:|---|---|
| `node_count(...).ok_or(Error::Merkle)?` | 196 | 993–997 | Converted residual is discarded; `done (idx,val,none)` |
| count/padding guard `return Err(Error::Parse)` | 200 | 966,980 | Both sides of the OR guard produce `none` |
| false verification `return Err(Error::Merkle)` | 203 | 992 | `done (idx1,val2,none)` |

Emission: `evidence/batch-merkle-20261108/NJS_emitted/raw/NJS_Extract/Funs.lean`. Its `verifier.candidate.batch_tree` maps `none` to `fail panic` (1045–1047), instead of returning `ok (Err ...)`. Four syntactic branches are three source exits, not four distinct source errors. The duplicate-leaf error **inside** the while loop and final `Ok(())` preserve their values.

The corresponding `Port3_NativeBatchBody` body contains the same defect (149,163,175,180 and the enclosing `batch_tree` match). Parameterized NJS copies also retain it. `NKT_DISCARDS.json` identifies four discarded residual-conversion occurrences, all in this same function; no additional discarded-residual family was found in the enumerated main corpus.

Existing LLBC was inspected without invoking Charon. `NKT_LLBC_REVIEW.json` pins the archive and verifies that `item_meta.source_text` is an exact substring of frozen Rust. LLBC statement 3442 calls `from_residual` into return slot0 at line196; statements3202/3285 and3414 write Err variants into slot0 at lines200/203. Charon therefore retains these error values. The loss occurs in the emitted Lean. This corroborates ruling (bc), without modifying or extending its trust classification.

## Row impact, with statement/closure evidence

`NKT_ROOT_REACHABILITY.json` covers **1,057/1,057 selected distinct roots** from the 553 CLOSED rows and three pending packets. It reuses checked raw-walker lists, verifies available uncompressed SHA sidecars, decodes NKI's `.xz.b64.txt` artifacts, and records four NKL lists recovered read-only from the existing host workspace. No raw walker, Lean compiler or binary was rerun.

Only two checked root closures contain the defective `batch_tree`:

* `AspisR1.NHS_CheckpointPacket.source` (TX1:186). Its statement consumes parsed, scan, preparation, constructor, allocation, pending/query and flush facts, and concludes the checkpoint writer packet. It never invokes or compares the rejected `batch_tree` Result. Its proof applies `NHS_NFWObligation.source`, `NHS_PendingSource.initial` and `NGC_CheckpointBridge.derived_packet`; the batch body enters transitively through configuration definitions. **INSENSITIVE to these three exits**, at this theorem's recorded statement. Citation: `evidence/prepared-close-20261106/NHS_CheckpointPacket.lean:11` and the named callees in its proof.
* `AspisR1.RPx_Deployed.deployed` (listed additionally for TX1:168/169/170). This is the conditional headline, with an explicit AeneasExtraction premise and accepted first/second native executions. It is not a total native `batch_tree` Result equation. The helper rows' actual queries/scalar/scalar_k roots have no `batch_tree` in their checked closures. **INSENSITIVE for the helper Result claims**; this does **not** certify the headline's frozen-source fidelity or justify ignoring rejected oracle prefixes. Citation: `evidence/replay-deployed2-20261027/RPx_Deployed.lean:40`, its `extraction`, `accepted1`, `accepted2` premises, and each helper's independent roots in `NKT_ROOT_REACHABILITY.json`.

Every other selected root has no `batch_tree` constant in its checked closure. This is stronger than textual non-occurrence in a theorem's surface statement. `NKT_AFFECTED_ROWS.md` enumerates the rows and exact roots. No newly CLOSED row is recommended for REOPEN on the **confirmed** defect. No global fidelity assertion follows from that statement.

TX1:083/TX2:055 and their graph ancestors are already OPEN in ledger19. They have no admitted exact-Result row theorem to revoke. Retain OPEN and require the explicit error/prefix transport of (bb)/(bc); do not substitute panic for returned Parse/Merkle. The node_count error may require a domain-unreachability argument on restricted canonical inputs; this audit supplies no new such lemma and takes no credit for it.

## Controls and false positives

`python3 evidence/emission-audit-20261109/NKT_checker.py --controls-only` passes all three controls. The positive control flags all three source exits (four branches). The normal-exhaustion branches of `verify_in_place` and `canonical_scan` contain zero loss hits. Internal `none`-propagation warnings remain visible; they are not suppressed to make a control pass.

All **85 site packets** in the main conservative corpus were reviewed, grouped by the 34 distinct flagged definition names. `NKT_REVIEWS.json` retains every occurrence, location, reason and source citation. Common false positives:

* validate_checkpoint_queries uses none as the precise Checkpoint error, reconstructed by its caller (`Port5Q2_ReaderValidate.reference`, `NJC_ValidateEmission`). NCO validate_ref likewise reconstructs NonCanonical(row,i).
* Normal iterator exhaustion becomes the caller's tail Ok/output/true/false. In-loop errors carry some residual; NCV predicates, the control_ref reference, decoder weights and decode_k follow this form.
* Borrow writeback passes none to next_back inside a returned function. It is not a pending Result.
* canonical_scan's nested completion tags preserve residuals; its outer tail is some(Ok()). `NKL_ScanModel.source` and `NKL_CanonicalInstallation.source` give the existing full Result equation at proof width57607.
* QueryGeometry's empty-flat early success and expand_semantic's final Length errors return direct Result values. challenge_qm31's error after the inner retry loop is some(Err()), not discarded.
* The apparent post-loop exits in verify_finish and the non-pool instruction branch follow loops excluded by deployed features. The corresponding cfg source locations are retained in `NKT_SOURCE_SITES.json`.

No other Result-loss pattern was confirmed in these reviewed sites. This is a bounded pattern audit, not a general theorem about every possible extractor defect.

## Inventory and unresolved completeness obligations: NKT-F2

The checker scans all **1,142 tracked Funs.lean files** plus **455 renamed/source-annotated modules** reached through the recorded import manifests. The raw superset has28,724 definition occurrences; exact file-byte aliases are grouped. The main inventory has6,574 distinct file/definition occurrences. Constants, generated trait dictionaries, library definitions and reference functions are retained conservatively, rather than discarded by a guessed native-function match.

`NKT_AUDIT.json` records source annotations, emission paths/hashes, frozen same-name/location candidate fn-body hashes where mapped, source scans and verdicts. Short crate-relative paths are resolved explicitly. A null frozen hash is **not a match**: it marks a reference/library/closure/constant or unresolved native association. The original annotation span hash is separate from the fn-through-closing-brace frozen hash. A hash of a same-name/location candidate does not itself certify the owner/source association. Historical line numbers alone are not body-identity evidence.

`NKT_EXTRACTIONS.json` indexes428 emission blobs:92 have hash-linked pin receipts,62 have same-packet tool metadata only,274 have no recovered exact tool-origin mapping. Same-packet proximity is not a tool-identity proof. In particular, normalized/parameterized historical bodies must be traced to their exact raw emission rather than assigned the current NCO binary pins by name. NHR/NCO's explicit accepted pins remain independently recorded in their original manifests.

The import graph uses the four recorded EXPECTED_IMPORTS manifests; ambiguous source filenames retain all tracked candidates. It does **not** claim that every retained historical source is the source of the selected olean. The selected object manifests remain pinned separately. A read-only attempt to recover adjacent sources from those selected host objects found only three emitted-source files, all matching their recorded object hashes (`NKT_HOST_READ.json`, `NKT_HOST_SOURCES.json.xz`).

**Remaining deliverable:** exact selected-source-to-object and raw-extraction/tool-origin recovery for every unresolved entry in the JSON artifacts. Until then this audit cannot meet the universal enumeration/source-pin requirement or issue a corpus-wide clean bill. This gap is reported, not converted into a new trust assumption or a row status change. Printing a Lean declaration cannot recover its historical extractor binary, and a new Charon run cannot reconstruct a missing historical Aeneas provenance chain; new Aeneas extraction is outside the zero allowance.

## Additional inventory gap: NKT-F3

Ledger19 CLOSED rows TX1:059/TX2:040 (`WideExact::to_limbs`) have empty `root_owners`, `kernel_roots` and certificate theorem lists; their owner role is a transparent certificate forest. The frozen function is the explicit array of eight stored u32 coordinates (`field/wide_exact.rs:238-249`), with no loop and no callee, so it is insensitive to the confirmed batch-tree exit loss. This source inspection is **not** a replacement theorem or a revalidation of those rows' closure credit. The missing named-root association is recorded for the lead; no ledger edit is made.
