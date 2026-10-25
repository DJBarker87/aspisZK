# Checked test-input contract and failed whole-parent optimization, 2026-10-25

No protocol/source closure. Historical25866 component context ONLY, not the
later4bb3 release source. This packet is retained to avoid repeating the same
failed proof strategy. The native constructor/claim late error cases remain open.

One source of repeated work was the TEST input generator any_e, which masks
all8 arbitrary u32s to canonical words and calls the real native from_limbs.
Its canonical-return contract passed (probe v2). Verified stubbing initially
failed compilation because native WideExact lacks kani::Arbitrary (v3); v4
verification was correctly rejected at its failed compile predecessor.

A separate verification-only native core copy APPENDS cfg(kani) Arbitrary for
the complete native E type, directly constructing its original8 fields from
raw words. No field/type/existing method is changed. Raw values are used ONLY
by contract havoc, then filtered by the CHECKED canonical postcondition before
any source arithmetic. All raw bit patterns are valid Rust representations
(the private canonical invariant is restored before protocol use). This is
not a simplified carrier, unchecked canonicality premise or deployed source
change. The checker strips the exact extension and compares the whole original
wide_exact file against25866. Other candidate-core source bytes are retained.
Adoption as production is neither needed nor proposed; any later source/runtime
association must explicitly retain these proof-only context qualifications.

The probe verified-stub smoke v6 passed0/47 checks. The generator contract was
then checked AGAIN in the actual complete constructor module context (parent
v2), rather than assuming a different module's proof was its producer. The
complete native constructor/transcript/gamma+kappa powers/original claim body
and the nine normal primitive cuts stayed unchanged. All29 possible point4
error columns, arbitrary full native inputs and174 state-return slots remained;
no narrower result was substituted to manufacture a pass. Only the checked
TEST-generator contract replaced repeated generator execution.

The complete parent v4 still hit its initial7GiB aggregate watchdog after
262.796417s at7708786688B sampled aggregate. Final peak RSS and swap are
UNKNOWN because time(1) was terminated. No solver verdict, source equality,
arithmetic/decoder/SDK/privacy/soundness result is credited. The parent source
extension and checked generator are NOT a solution to the actual source gap.
No additional cap/unchanged retry is authorized by this packet.

Validation is source-only focused-extractor-proof-packet-v1 with exact commands,
source/tool/import hashes, full source snapshots and receipts. Generator-only
passes use under1 second; core-copy compilation was3.849914s/696745984B/swap0.
Parent compile v1 passed0.663588s/163430400B/swap0; its generator contract v2
passed0.663164s/23166976B/swap0; full parent compile v3 passed1.106141s/
542228480B/swap0. All jobs local,sequential,atomic shared lock,explicit caps,
optimized native Kani0.67.0,default checks plus contracts/unwinding assertions.
#print axioms:N/A,no Lean theorem/custom axiom. No production edit/ELF claim.

The whole-parent attempt is stopped. Reuse the already checked constructor
call-site contract, original/reference claim normal-return equivalence and
Lean loop composition, while proving concrete source/callee instances and
later-source association. Another larger whole-stage SAT retry is not the
next deliverable. Actual S1/S6 and the100-bit target remain not established.
