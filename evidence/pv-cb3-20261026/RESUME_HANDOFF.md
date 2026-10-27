# Resumed CB3 handoff

Branch codex/pv-cb3-20261026, resume base54f2ac877f.100/100Lean attempts
charged;71passed. Kani2/15: queue stopped on builtin memcmp unwind17
configuration failure,13unspent as required. Next unused ID35702; no remaining
Lean budget. Retired uncharged IDs35600,35612. No checked source counterexample.

Worker candidate rows4→5: V195/op51 is now discharged for arbitrary extracted
carriers, with complete Result and no canonicality or desired-output premise.
The new native harness directly constructs all eight unconstrained u32 fields;
it does not call WideExact::new.170checks pass. See35603.json and
kani-wide-arbitrary-001/collected-receipt.json. Older published statements stay
unchanged; use PV_CB3_Op51Arbitrary.op51_source for unrestricted coverage.

Op249's full staged by-value reference is extracted and has checked complete
Result/totality, typed pass/carry, final wrap, byte-word value and canonical
constructor links. PV_CB3_StagedKernel.source passed35686. No shipped/reference
association is claimed: V256 remains OPEN. Next: a compositional native gate
for shipped=staged reference, followed by unrestricted op249_source. Do not
rerun inherited whole-sampler timeouts unchanged. Op223 remains blocked by the
escaping-reference loan-validation guard; no weakened extractor was used.

RESUME_ROWS.md/json is the full op→row→status→theorem→receipt table. Native
effects op26/30/31/32/36 are explicitly deferred to pv-runjoin and remain OPEN.
Sibling global scan revisionaadb0e1407 only found op229_source; dedup V246.
Recount2 plus this worker: candidate44→45, OPEN106→105, independent47→46,
excluding live sibling additions. Endpoint premises removed/added/changed0.

Frozen39:25focused receipts reused,14missing modules checked once. Audit35701
passed68imports/78axiom targets, wall1.55s peak4276564KiB swap0, standard axioms
only. RESUME_FINAL.json embeds exact target/revision/hash and result;
RESUME_FINAL_MANIFEST.json validates source/receipt identity. Failed receipts
including sorryAx output from rejected proofs remain evidence only. Every
currently shipped new Lean source has a matching green source-hash receipt.

Only own rebuildable host kani-target/charon-target were removed after evidence
collection; shared/candidate objects, source, receipts and keys retained.
No tracked crates/programs, release pins, old PV_CB3 statements, simulator,
observer or privacy endpoint changed. Target not established. E1/E2, RunJoin,
L1/L2/L3, client-route and whole endpoint closure remain open.
