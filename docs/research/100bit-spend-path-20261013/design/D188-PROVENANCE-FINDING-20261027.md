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
