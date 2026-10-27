# Finding D188-P2: the PublicPreparation model is extracted from a retired verifier path (lead, 2026-10-27)

Status: FINDING for the owner. No claim is withdrawn silently; this note
states exactly which attribution is not established.

## What was checked (extraction-repro1/2, XRa_/XRb_, merged)

- The historical extraction tools were recovered: Charon rebuilt
  byte-identical to the receipts (cb50ff16...); the patched extended Aeneas
  source rebuilt (tree 3be6820e...; fresh binary reproduces every historical
  generated output byte for byte).
- Release Charon on the frozen compiler-input pin 4bb3b3f51e16b4525f1d10336e
  2b0bcbbd775387 succeeded: LLBC 0814e4ec..., 533 functions, 104 types.
- The exact pinned Aeneas FAILS on the release LLBC: compact::check_values
  (InterpReduceCollapse Not_found), then verifier::echeck
  (InterpJoinCore.Distinct). So the release verifier path has never been
  translated whole by the pinned translator; the historical cohort was built
  from kits with opaque child boundaries.
- Of the eight source cuts that differ between the cohort source and the
  release source (L8a_): verifier_error is identical (the extra variants are
  cfg(prover), disabled); verify_observed is an opaque child in both;
  FIVE are genuine interface/carrier differences:
  - dot_type: historical canonical::Dot has sums and count; release has sums
    only (private push-count check removed).
  - prepared_claim: historical consumes gamma:WideExact; release consumes
    g:&[WideExact;29] (powers array).
  - query_geometry: release adds a line_z:Vec<M31> cache field.
  - tx1: historical verifier.tx1 accepts k<=22 and dispatches the retired
    eight-way path; release candidate.tx1 requires k=SPLIT, the compact
    parser, expansion, batched binary multiproofs and deferred weights, and
    its checkpoint binds compact stored bytes.
  - tx1_finish: retired helper; no release counterpart.

## What this means

The PublicPreparation / ExtractedTx1Model / S1 semantic-prefix part of the
Rc10 closure models the retired verifier.tx1 path, not the release's
candidate.tx1 path, at these five interfaces. Theorems proved about that
model are mathematically valid but their attribution to the deployed ELF is
NOT established at those interfaces (AGENTS.md section 6: a historical proof
is not attributed to a different implementation because a name is
unchanged). The compact/batched path itself (Op5T stageBatch, the batched
multiproofs, the checkpoint binding, the finish family) is modelled by
other extractions and is not the subject of this finding; the question is
the boundary between the semantic prefix model and the release's
preparation/query/finish path.

## Options

A. Fix the pinned translator so it translates the release path whole
   (compact::check_values, verifier::echeck). A toolchain change: the
   extraction pin and the D188 item would have to be re-pinned; owner
   approval required; unknown effort.
B. Prove explicit association theorems between the old-path model and the
   release path for the five declarations (e.g. old Prepared::new equals the
   projection of the release Prepared::new with its scratch array; the
   prepared_claim powers-array argument equals the successful result of
   powers 29 gamma; Dot projection; line_z as a cache invariant; candidate.
   tx1 vs the retired dispatch). Real proof obligations of unknown size.
C. Re-extract the release path as a KIT with opaque leaves exactly at the
   two failing functions (as the historical extraction did), obtain complete
   release Types/Funs for candidate.tx1 and its preparation/query/finish
   children, then do B against the release definitions directly, with the
   two leaves handled by P6/Kani or a smaller kit.

## Recommendation

C now (extraction-repro3 is running it; no tool change, no trust change),
then B. A only if C cannot place the boundary. Until B is done, the
headline's "deployed" attribution is qualified at these five interfaces,
and the ledger gains a deployment row for the association obligation at the
next recount.

## Update 2026-10-27 (XRc_/XRd_): route C exhausted at the pinned translator; route C' adopted

- The original release LLBC (0814e4ec...) was produced with the historical
  kit's opacity selectors and lacked the needed bodies. A second Charon run
  on the identical source with the identical Charon binary and selector-only
  changes produced LLBC 80465ea3... with every required body (approved by
  the lead as within the D188 boundary: same tool, same source).
- The pinned Aeneas cannot translate SIX release functions:
  compact::check_values, verifier::echeck, compact::expand_values,
  candidate::wide_view, checkpoint, prepared_claim (the last two newly
  exposed by the complete LLBC).
- Route C' (no translator change, no trust change): extract everything else
  with those six as opaque leaves; model the six by the P6 route (owned
  reference + Kani shipped == reference + Lean model with correspondence);
  then prove the association items against the release definitions.
  extraction-repro5 (XRe_) is running it.
- Route A (translator fix and re-pin) remains the fallback and needs the
  owner's approval; it is not recommended while C' is open.

## Update 2026-10-27 (XRe_/XRf_): seventh untranslatable body; convergence protocol

- The six-leaf kit was not call-closed (a library call, Iterator::copied,
  had been excluded); XRf_ fixed that (1,545 call sites, no missing
  callees). The pinned Aeneas then failed on a SEVENTH release body,
  r1_semantic::claims. Kani stages for the compact leaves pass (10/10).
- Ruling: extraction-repro7 converges the leaf set in one job (12
  invocations, add-leaf-and-retry). If the leaf count passes ten before
  emission, the job also writes the route-A case (translator upgrade and
  D188 re-pin) for the owner. Each leaf is a P6 obligation and a ledger row.

## Update 2026-10-27 (XRg_): leaf count passed ten; route-A evaluation started

extraction-repro7 used all 12 invocations: the call-closed release kit now
needs TWELVE opaque leaves (compact::check_values, verifier::echeck,
compact::expand_values, candidate::wide_view, checkpoint, prepared_claim,
r1_semantic::claims, decode_k, validate_record_fields, semantic_boundary,
canonical::Dot::push, the circle_sample closure) and the twelve-leaf LLBC
is not yet run through Aeneas. The failures fall into a few translator
classes (loop-context borrow collapse, join mismatch, borrow/value
bottoms, unsupported Arrow types), none a mathematical counterexample.
Route-A case: evidence/extraction-repro7-20261027/XRg_ROUTE-A-CASE.md.
extraction-eval1 (XRh_) runs the twelve-leaf kit once more with the pinned
tool and, separately and in isolation, evaluates the newest Aeneas/Charon
on one minimised reproduction per failure class and, if those pass, on the
full kit. Evaluation only: no pin changes, nothing it emits is imported or
cited. Re-pinning D188 to a new translator remains the owner's decision.

## Update 2026-10-27 (XRh_): route C' unblocked; route A not pursued

- With the PINNED tools, the call-closed twelve-leaf release LLBC emitted
  COMPLETE Types/Funs (exit 0, first attempt; XRh_PINNED-RESULT.md). Route
  C' proceeds: extraction-assoc1 (XRi_) compiles the emitted definitions in
  an isolated namespace and proves the association items against them.
- Route A evaluation (newest published Aeneas nightly-2026.10.27 with its
  matching Charon): three of five failure classes pass, borrow/value is
  partial, the Arrow/iterator signature check still fails, and a full
  no-leaf release extraction emits nothing (five more control-flow
  limitations). The newer backend needs Lean/Mathlib 4.35 and replaces the
  inductive Result with an interaction-tree effect type, so old proofs that
  case-split on ok/fail/div do not transfer. Lead ruling: route A is NOT
  recommended and NOT requested from the owner; the pinned toolchain stays.
  Evidence: evidence/extraction-eval1-20261027/XRh_ROUTE-A-EVAL.md.

## Update 2026-10-27 (XRi_): release definitions need hand-supplied externals

extraction-assoc1 could not elaborate the emitted release Types: their
imports TypesExternal/FunsExternal exist only as Aeneas axiom templates. No
association proved. Ruling (extraction-assoc2, XRj_): supply the externals
as definitions, never axioms: library operations reuse the repo's existing
pinned external definitions; each of the twelve opaque leaves is defined as
the Lean model of its owned reference, with its Kani bridge recorded as an
open P6 obligation. Then prove the association items against the emitted
release definitions.

## Update 2026-10-27 (XRj_): emitted release Funs needs adapters

extraction-assoc2: external Types and the unchanged release Types compile;
FunsExternal 65/103 defined (4 leaf models); 7 model laws; per-iteration
Kani 9/10. The unchanged emitted Funs does not compile against the pinned
Aeneas library: a mutable-iterator ABI mismatch, a closure return-state
mismatch and `compact` namespace shadowing. These are tooling seams, not
semantics (likely why the historical producer was an adapted union). Lead
ruling (extraction-assoc3, XRk_): resolve through externals with the
emitted signatures and namespace arrangement first; otherwise only a
scripted, reproducible, audited transform limited to name qualification or
signature adaptation, every changed declaration listed with before/after
text (XRk_ADAPTERS.md). No change to function-body logic.

## Update 2026-10-27 (XRk_): release definitions compile; adapters need proofs

extraction-assoc3: all 103 externals supplied (twelve leaf models defined
from the owned references), the emitted release Funs compiles through a
deterministic, documented adapter transform (XRk_ADAPTERS.md,
XRk_adapter_changes.json; raw input retained by hash). Local emitted-model
associations proved: PreparedScratchProjection, PreparedClaimPowers-
Association, local DotCountProjection laws, CandidateTx1AcceptedPath and
AcceptedCandidateCheckpoint local projections. Lead review: the adapters
are more than renaming; they restructure mutable-iterator/closure state
restoration to fit the pinned library's fixed trait signatures. Ruling:
each adapter needs its own proved Result-and-state equivalence to the
emitted original semantics before any association through it is credited
(extraction-assoc4, XRl_). No D188-P2 row is closed yet.

## Update 2026-10-27 (XRl_): adapter proofs caught a non-faithful adapter

extraction-assoc4: state laws proved for six adapters (enumerateNext,
intoIter, fromFnState, revRestored, enumerateRestored, closure_1 FnMut) and
the FnOnce/dropped-callback projections. The reverse adapter (reverseNext/
next_back) is NOT universally faithful: on an exhausted singleton iterator
the original returns None and the adapted model returns Some true. It is
faithful on the cursor-zero domain that a fresh iter_mut supplies. This is
exactly why adapters were required to carry proofs. extraction-assoc5
(XRm_) must show every call site of that adapter receives a cursor-zero
iterator, or report the site (the adapter would then be replaced, not
trusted). Also open: the native producer invariant that Dot operands are
canonical. Geometry cardinalities and Dot-history laws proved.
