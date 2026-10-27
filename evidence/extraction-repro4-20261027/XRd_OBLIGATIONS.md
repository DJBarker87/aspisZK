# Remaining release/cohort obligations

**Target not yet established. No listed function association is discharged.**
These are implementation/refinement gaps, not cryptographic assumptions. The
ledger and contract are untouched. Estimates below are focused proof-target
ranges, not measured runtimes, and overlap.

## Extraction predecessor

The old LLBC body's absence is resolved at the structured-LLBC layer:
80465ea3… pins the identical release source with the approved selector change.
Pinned Aeneas cannot emit its Types/Funs: checkpoint context mismatch at
verifier.rs:330, then prepared_claim's missing abstraction-map entry after the
checkpoint-only split. Both are NEW failures beyond the four mandated leaves.
The smaller artifact 370b8a0a… is INCOMPLETE and is not promoted to release
success. No source, translator, library, feature or version change was made.
Need a separate approved strategy for these two translator failures; no
additional opacity is silently accepted as a complete requested kit.

## Requested items, in priority order

1. **Semantic/public/hash dictionaries.** Relate the release dependency-crate
   carriers and every dictionary field to the historical inlined carriers,
   with exact argument/reply/error/ordered-effect laws. Affects L080–082,
   L139–146, L157/L181, installed preparation. Size 4–8 targets, plus semantic
   relation proof. No substitution of coherent WideExact for an unresolved
   generated external template is installed.
2. **Prepared::new projection.** Full outer Aeneas Result and inner Rust
   Result transport under related sem/view/hash dictionaries, arbitrary
   scratch `[WideExact;29]`; on success identify scratch with successful
   powers29(gamma) and use the SAME gamma/kappa for prepared_claim. Preserve
   early failures and error order; do not assert successful powers on early
   error. Affects L122–124, L130–132, L139–141, L157/L181 and S1 installed
   preparation. Size 4–8 targets after valid generated declarations exist.
   No concrete new declaration exists to type-check this Prop in this round;
   no placeholder or assumed whole-result equality is created.
3. **prepared_claim.** Relate old gamma argument to new powers-array argument
   equal to successful powers29(gamma), all six scalar selections, seven
   parts, kappa powers, Dot push/finish, short-circuit errors and effects.
   Affects L139–141, L144–146, L157/L181 and S1 installation. Size 4–10 targets
   plus arithmetic children. NEW direct translator blocker: Not_found in
   InterpReduceCollapse.ml:1991, while remapping shared-borrow abstraction IDs.
   XRd_006 captures the final contexts, including y1/g borrows and parts write.
4. **QueryGeometry.** Project start/inverses, prove the line_z cache invariant
   for every reached query, and cover failed construction/range/zero inverse
   paths. Affects L130–132, L149–150, L157/L181. Size 3–6 targets. Its LLBC body
   is present; successful symbolic processing before a later exception is
   not an emitted/checked Lean definition or an equality proof.
5. **canonical::Dot.** Count-dropping projection, push/finish with canonical
   limbs, enclosing 4096-term bound, no-wrap invariant and failure/ownership
   frame. Affects L128/L142/L147–148, S5 association and L157/L181. Size 4–8
   targets; historical opaque kit still lacks the old extracted Dot body.
   New LLBC includes Dot and methods; no new Lean output is emitted.
6. **BatchedWeights.finish/query_loop.** SAME query sequence/accumulator,
   deferred versus eager/eight-way weights, restored state and all failures.
   Affects L125/L128/L142–143/L147/L149–150/L157/L181. Size 8–16 targets;
   overlaps S7/S8 and does not replace their concrete source obligations.
7. **candidate.tx1 versus retired dispatch; checkpoint.** Restricted accepted
   domain/representation, exact compact expansion and authenticated physical
   bytes, SPLIT and binary multiproof dispatch, same saved CP and ordered
   oracle effects. No universal old/new equivalence. Affects L091–109,
   L122–124, L130–132, L139–141, L149–150, L157/L159/L180–188 and S1 installed
   preparation. Size 10–20 integration targets after children. NEW checkpoint
   loop context failure blocks the complete kit (XRd_002/003).
8. **verify_observed.** Remains opaque in the inherited selector set. Relate
   actual semantic_rounds/verify_finish including all earlier rejection
   effects. Affects L144–146/L157/L181. Size 4–8 targets plus semantic cone.

## Four deliberately opaque leaves

compact::check_values: canonical compact scan, lengths/limbs, errors and
frame (2–4 targets); verifier::echeck: exact WideExact high/low canonicality,
errors/read frame (2–4); compact::expand_values: checked restoration, low-half
copy/zero-high-half, length/overflow/alias frame (3–6); candidate::wide_view:
exact borrowed View slices/layout/restoration/error frame (2–4 plus caller).
Each needs a smaller pinned kit or actual-source P6/Kani proof. No Kani is
allowed here. Affects L099/L108–109/L139–148/L157/L181/L186–188 as detailed
in XRc_OBLIGATIONS.md; no new leaf is hidden inside these four obligations.

## Coverage, trust and non-vacuity

All 45 Types/87 Funs of the coherent producer are retained individually in
XRd_declaration_diff.json. Additional helper/dictionary/formatter pairs need
transport or justified exclusion when release declarations become available.
No whole-prefix formatter deletion or standard-axiom approval is inferred.

No new concrete typed function Prop/theorem or XRd_Association.lean is supplied:
those declarations do not exist in emitted Lean. This is an explicit incomplete
deliverable under common rule4, not a declaration hidden as an axiom or free
callback. XRc's checked error-carrier inverse remains reused without rerun.
No top imports a new module. Actual Rc10_Top.deployed and ledger are byte
unchanged; removed/added/changed 0/0/0, delta T0/P0/G0/C0. No same-witness joint
inhabitant is constructed. No new #print axioms result exists (no new theorem).
Frozen3, approved two-transaction game and RuntimePersistence are retained.
