# LPa P6 leaf ledger

**Target not yet established. Actual-top premises removed: zero.**
Before/after AspisR1.ARX_Root.deployed are byte-identical (LPa_BEFORE.lean.txt,
LPa_AFTER.lean.txt). Ledger: atomic quantified families, SAME witness, shared
families once, L185=L159 alias; removed/added/changed0/0/0, deltaT0/P0/G0/C0.
Frozen3, RuntimePersistence, the approved game and security target are unchanged.

A **closed stage** below is an exact native-library comparison on the specified
input domain. It is not a whole-leaf/source-to-ELF certificate. Kani certificate
names are cited as evidence, never introduced as Lean axioms. The existing
XRk leaves were not edited; new LPa proofs connect their computations to
recursive loops/folds. The top does not import LPa or obtain a new premise
instance from these results. No full native leaf or deployment row is credited.

| Leaf | Overall bridge status | Closed / checked pieces | Exact open stage |
|---|---|---|---|
| compact::check_values | **partial** | K001 direct arbitrary16-byte stage equals owned reference; K002 two-chunk composition; K003 every length0..31 incl. tail. LPa.Check.shipped_leaf_model/loop_eq_fold, accepts_iff/rejects_of_bad_stage; little-endian four-byte bound and word-value correspondence. | Native complete464-byte loop/read-only carrier association and installation in the SAME actual release execution. The symbolic Lean loop bound is length/16, not a fresh whole-Rust proof. |
| verifier::echeck | **partial** | K008 arbitrary32-byte chunk/both k values; K010 direct two-chunk composition. LPa.Echeck actual-model loop/fold and exact rejection laws. | K009 variable0..63 tail domain TIMED OUT. Actual928-byte/general source loop/carrier association and full tail transport remain open. |
| compact::expand_values | **partial** | K004 arbitrary16->32 stage plus live8-byte prefix/suffix; K005 alignment rejection and K007 output-size rejection on464/928 capacities preserve destination. LPa.Expand existing-leaf/byte-loop/fold, length, low/high half, exact928-byte target fold. | K006 indexed stage in arbitrary464/928 buffers TIMED OUT. The byte-map versus29 source row stages, full-buffer borrow/frame and native-to-model association remain open. |
| candidate::wide_view | **partial** | K015 calls the actual library at57607/13831/928 bounds with arbitrary inactive32 bytes; checks error/value and borrowed pointers/lengths. LPa.View.frozen_success/frozen_reject derive all slice calls at the actual proof length. No loop exists in this leaf. | Native frame/extensionality for arbitrary non-inactive proof bytes and full native Slice/borrow/heap interpretation. The passing K015 fixes those bytes to zero; it is not the previously failed arbitrary-whole-proof shape. |
| r1_semantic::claims | **blocked** | LPa.Claims.leaf_eq_loop/fromRecord_spec prove the EXISTING model equals the actual three-step decode loop and loop_eq_fold, including early Err/fail/div. | K019 direct actual3x29 decoder/storage with one arbitrary canonical lane in point0 TIMED OUT. General87-lane native allocation/write/ownership/source association and Prefix provenance remain open. point2 harness is present but UNRUN; its slot was replaced by K020. No supplied/predecoded child or allocator stub is used. |
| ValidatedRecord::decode_k | **partial** | K011 direct N1 framed37 domain, arbitrary row/offset, incl. overflow/range/rejection; K012 direct N29 guard on short frame. LPa.Decode actual existing leaf equals N-stage value loop/map/fold plus firstBad recurrence; accepted values/length/error bound and byte/word laws. | Successful29-value loop on the full record, nonzero reached offsets29/58, native output-array/carrier association and validation-token provenance. K011 only succeeds at offset0 in its37-byte frame. |
| validate_record_fields | **partial** | K013 arbitrary32-byte stage/all rows; K014 direct64-byte first-error/index composition. LPa.Validate actual-model loop/fold and exact first error; portable index guard cannot fail on actual largest3712-byte payload. | Full116-value native loop/byte/error carrier association and caller installation. Unrestricted gigantic Slice correspondence is explicitly NOT claimed; see LPa_PORTABILITY-BOUND.md. |
| semantic_boundary | **partial** | K020 actual QM31::add stage vs independent canonical u64 formula; actual accumulator/coefficient arbitrary canonical and output coordinate arbitrary. LPa.Add.word_val_canonical plus field/fold canonical invariants, LPa.Boundary.loop_eq_model/loop_eq_fold/loop_pure; actual bound28 and seed coefficient0 counted twice. Zero polynomial accepted. | K016 whole28 comparison TIMED OUT and was replaced by the isolated K020 stage. Remaining: SAME actual decoded-array/field-carrier and canonical-producer association to connect that canonical stage domain to the accepted source caller. |
| canonical::Dot::push | **blocked** | LPa.Dot.shipped_leaf_model/loop_eq_fold/model_total connect the existing four-cell wrapping model to its loop. | K017 arbitrary canonical Q operands/arbitrary sums direct library update TIMED OUT. Native raw producer/fold update stage and canonical-operand/history joins remain open. No copied raw-fold excerpt is promoted to a direct native bridge. |
| circle_sample closure | **partial** | K018 actual circle_sample on zero block, both rows, reaches real fallback without a stub. LPa.Circle.leaf_eq_reference/error_independent cover both modeled errors. The closure has no loop. | General native anonymous-closure/capture association and the algebraic-model versus actual fallback/inverse-chain helper binding. Zero-block reachability is not a full arbitrary sampler association. |

## Correspondence and evidence

LPa_CORRESPONDENCE.md explains statement-by-statement associations;
LPa_line-correspondence.json pins all ten frozen source/reference ranges and
hashes, existing Lean owner files and LPa theorem files. The native crate uses
the shipped functions as a library in its own frozen workspace with cfg(kani)
harness additions. No shipped computational function is copied into a test
implementation, stubbed, or changed. References are safe owned computations.
All7978 pinned source inputs hash-match except the seven authorized cfg-only
parent hooks; the seven LPa harness files are additional inputs. Removing hooks
recovers exact frozen source bytes and original production line positions.

LPa_KaniSummary.json:20/20 runs,15PASS/5TIMEOUT(K006/009/016/017/019),
835.968536879s verifier/compile wall sum, peak RSS6437012KiB,
cgroup peak6608384000B, swap0. No cap/timeout increase or unchanged timeout retry.
The duplicate K001 orchestration was refused before invoking Kani and is not
additional validation. K017's exact host receipt/sources were collected after
its running driver was paused; no second native run occurred.

Lean:60/60 attempts, including11 unchanged prerequisite rebuilds, errors retained.
L060 batches89 new theorem names and ten existing leaves; only
propext/Classical.choice/Quot.sound. Failed diagnostic sorryAx outputs are
excluded, not imported or accepted. LPa_Verification.json is authoritative for
counts, source/dependency consistency and resources. No new trust axiom.

## Non-vacuity and deployment gate

LPa.Nonvacuity checks actual modeled empty scan/validation success and a reached
invalid-row decoder error. LPa.Boundary.zero_accepted checks the actual28-entry
zero polynomial by symbolic replicate/fold induction. Native domains have
concrete witnesses: canonical zero limbs, row25/offset0, lengths16/32, frame
index0, both circle rows; K020 also admits nonzero canonical limbs. These are
local witnesses, not a SAME-witness joint inhabitant of the security top.

The required ELF gate is **BLOCKED**. LPa_SBF_default failed on native serde_json
build-script linking (`rust-lld`: std::system_error, Resource temporarily
unavailable) within TasksMax64. No ELF was produced; devnet/Pool were not
launched. No host/launcher repair or cap increase is attempted (local-lean5).
The three hashes are inherited only, not freshly confirmed. See
LPa_SBF_BLOCKER.md. No whole release replay, source-to-ELF proof, security-top
axioms audit or formatter reachability result is claimed. XRm's two leaves,
association files, other workers and all wallet/account keys are untouched.
