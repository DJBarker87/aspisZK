# Release/cohort association obligations

Target not yet established. These are implementation/refinement obligations,
not newly adopted cryptographic assumptions. No listed row is discharged by
an extraction invocation. The unchanged ledger remains authoritative; the
links below identify affected families rather than adding ledger rows.

## Checked isolated pair

XRc_Association.VerifierErrorAssociation is proved by
XRc_Association.verifier_error_association (XRc_L001, no axioms). The release
enum declaration is copied exactly under XRc_Release; both directions of
constructor-preserving carrier transport are explicit. This proves no
function's error mapping/order and removes no ledger/top premise.

## Required-body availability (blocking)

Pinned LLBC 0814e4ec… contains no body for prepared_claim (240),
QueryGeometry::for_range (12), checkpoint (18); fast_pairing was wholly opaque.
The full required kit cannot be obtained by masking that LLBC. Need a ruling
on rerunning the exact pinned Charon on identical release source/features,
with changed kit selectors. No source text is reinterpreted as structured LLBC.
Estimate: one lowering and one translation, if no further translator failure.
Affected: L186–188 and the concrete producer association beneath L078–080,
L099, L139–148, L157/L159/L181–185. Existing compiler trust L189 does not prove
this association.

## Independent leaf obligations

- **compact::check_values** (Fun26): preserve canonical compact QM31 scanning,
  short-circuit/error identity and input frame for all slices, including bad
  lengths/limbs. Body omitted deliberately. Deliver a smaller pinned kit or
  actual-source P6/Kani certificate; this round has zero Kani allowance.
  Affects L108–109, L099, L157/L181 and associated entry/scan source instance.
  Estimate: 2–4 focused proof targets plus an installed-call bridge.
- **verifier::echeck** (Fun27): full canonical WideExact high-limb/low-limb
  checks, Result error mapping and read frame, on the exact carrier and
  dictionary. Also requires smaller kit or P6/Kani; remains separate from the
  compact scan even if both ultimately check canonicality. Affects L108–109,
  L148 and the L157/L181 source instance. Estimate: 2–4 focused targets.
- **compact::expand_values** (Fun40): XRc_001 failed in its zip of
  chunks_exact(16) with chunks_exact_mut(32), not in either requested opaque
  leaf. Need checked output restoration, logical-value low half copy and
  zero high half, length/error/overflow behavior and alias/ownership frame.
  XRc_002 additionally masks this body solely as boundary bisection. Affects
  L099, L139/L144–148, L157/L181, L186–188. Estimate: 3–6 focused targets.

- **candidate::wide_view** (Fun42): XRc_002 fails while returning the borrowed
  reconstructed View, with "There should be no bottoms in the value"
  (candidate.rs:76–88). XRc_003 masks it as the second/final bisection.
  Require the exact slices/borrow restoration, fixed logical layout and
  error/alias frame in a smaller pinned extraction or actual-source proof.
  Affects L099, L139–148, L157/L181 and source association L186–188.
  Estimate: 2–4 focused targets plus preparation caller bridge.

## Carrier and dictionary transport

1. **Semantic/public and digest dictionaries.** The historical kit inlined
   aspis_core and pool_v1; release uses dependency crates. Relate the exact
   physical semantic-public payloads and all child dictionary fields, digest
   arguments/replies and ordered calls, not just similarly named types.
   Affects L080–082, L139–146, L157/L159/L181–186. Estimate: 4–8 targets,
   excluding proof of the underlying semantic relation.
2. **Prepared::new and scratch/error transport.** Historical return is
   Result<Box<Prepared>,Error>; release additionally returns the backward
   scratch [WideExact;29]. Prove the projection law on related sem/view/hash
   dictionaries with arbitrary initial scratch; define both outer Aeneas
   failure and inner Rust error transport. Early errors do not return the
   successful powers array. On success bind scratch to powers<29>(gamma)
   and prepared_claim at that same gamma/kappa. No arbitrary scratch equality
   or acceptance-only equality is asserted. Affects L122–124, L130–132,
   L139–141, L157/L181 and the S1 installed preparation association.
   Estimate: 4–8 targets after concrete release extraction.
3. **prepared_claim.** Old child takes gamma; release takes &[E;29]. Relate
   g=powers<29>(gamma), all semantic terms/parts, kappa powers and exact
   failure order. This is a changed interface, not a name-only transport.
   Affects L139 and L144–146; estimate 4–10 targets plus arithmetic children.
4. **QueryGeometry.** Release adds line_z cache. Show projection of start and
   inverses, range validation and cache invariant for every reached query,
   including failed construction. Affects L129–132, L149–150, L157/L181;
   estimate 3–6 targets.
5. **canonical::Dot.** Old source tracks count; release has sums only. Need
   enclosing accumulator bound and canonical limb/no-wrap invariants for
   reachable calls, then projection of push/finish. Historical opaque boundary
   supplies no extracted old Dot body. Affects L128/L142/L147–148 and S5
   source association; estimate 4–8 targets after a separate old/release kit.
6. **BatchedWeights.finish and query loop.** Relate deferred weights to the
   historical eager/eight-way continuation on the SAME query sequence and
   accumulator, with all mutable restoration and failure behavior. The old
   tx1_finish declaration has no release counterpart. Affects L125/L128,
   L142–143/L147/L149–150 and L157/L181; estimate 8–16 targets, overlapping
   existing S7/S8 work rather than replacing its concrete source obligations.
7. **candidate::tx1/checkpoint.** Historical tx1 dispatches k<=22/eight-way;
   release requires k=SPLIT, compact layout, expansion and binary batched
   multiproofs. Require an explicit restricted-domain representation relation,
   exact authenticated physical bytes, checkpoint format and ordered oracle
   effects. Universal old/new acceptance equivalence is not proposed.
   Affects L091–099/L100–109/L157–159/L180–186; estimate 10–20 integration
   targets after existing parser, multiproof, query and checkpoint children.
8. **verify_observed.** Opaque in inherited kits. Need exact association of
   refactored semantic_rounds/verify_finish including early rejection effects.
   Affects L144–146/L157/L181; estimate 4–8 targets plus semantic cone work.
9. **Remaining declaration pairs.** XRc_cohort_inventory.json enumerates ALL
   45 selected Types and 87 selected Funs declarations, including helper loops,
   dictionaries and formatter families; they cannot be omitted merely because
   not one of the eight highlighted cuts. Namespace/type/dictionary transport
   or exact source-owner exclusion is required for each reached declaration.
   Formatter native proof helpers require reachability audit, not blanket
   standard-axiom approval. Size cannot honestly be estimated until the
   required release kit exists and declaration pairing is complete.

Estimates are engineering ranges, not measured proof runtimes, and overlap;
do not sum them as independent new obligations. S1/S2 results about historical
preparation/caller interfaces do not automatically describe release candidate.tx1.
Session A's proof files and candidates remain read-only. No change to frozen3,
RuntimePersistence, the approved game, security target or ledger is proposed.
