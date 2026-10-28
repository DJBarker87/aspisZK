PILOT RESULT: **partly**. Fixed-array Result codec leaves compose, but this job does not complete the requested vertical slice or establish headline closure.

# NCP composition pilot


Result-returning slice codecs and Vec output; U02 digest -> U03 afterstate/live/late -> U05 ASF8. Contracts and per-shape controls precede caller credit. Frozen Rust 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; headline AspisR1.RPx_Deployed.deployed.

Budget: 70 Kani, 60 Lean; one admitted capped scope at a time. No inherited LPb stages credited.

Stage 1: Result/slice shape admitted in the tested one-byte context: K001 inverted ensures FAIL; K002 weak callee PASS; K003 real caller PASS; K004 weak stub caller FAIL; K005 modifies violation FAIL; K006 actual mutation PASS.

Vec shape NOT admitted: K007 inverted ensures FAIL (78.821s solver); K008 weak callee PASS; K009 real caller PASS; K010 stub caller CODEGEN ERROR: Result<Vec<u8>,u8> does not implement kani::Arbitrary. K011 unlisted slice mutation FAIL; K012 real mutation/Vec return PASS. K010 is not a passing negative control. No Option<fn> used.

The narrow body checks do not establish large-buffer or whole-codec contracts. No native row becomes unconditional from these controls.

## Obstructions and recommendation

- Vec output: K010 cannot construct an arbitrary Result<Vec<u8>,u8> under stub_verified. K007/K011 detected the intended bad ensures/frame, and the real caller passed, but codegen failure is not a successful weak-contract negative control. No Vec composition admitted.
- For/enumerate: pinned loop-contract compiler crashes for K032/K033. The actual digest encoder is tested separately at K070; no whole native buffer unwind is substituted.
- Borrowed record while: K054/K055 compiler error on unsupported invariant dereference. A cfg-only local alias gets past codegen, then K066 times out at 90s (wall98.878s, peak6,531,304KiB, swap0). The own queue incorrectly submitted its matched negative K067 before the timeout was classified; it was stopped with SIGTERM (CBMC status15) and receives no credit. Queue pause now prevents another submission; replacement is one arbitrary-prestate iteration K068/K069 plus the existing NBH_Frontier.afterstate_loop induction. This replacement does not provide proof_for_contract for the whole validator.
- Exact8/32: K046-K053 were bounded harness observations whose function contract omitted the bound. They are superseded by K058-K065 with the EXPLICIT contract precondition bytes.len()<=33. Every reached afterstate exact call is length8 or32 (NCP_CallerDomains proves the model ranges); there is no unbounded-length native helper claim or N=4 credit.

Recommendation: retain the checked codec leaves and the model-side discharge; do not roll out the medium to full buffer encoders/validators on this toolchain. Isolate the iterator/invariant compiler failures and Vec Arbitrary gap, then validate any repaired, pinned toolchain with the same controls. Existing Lean loop induction and native one-step bridges remain useful; they do not magically supply Kani proof_for_contract.

## Native caller rows

No existing U03/U05 CLOSED-CONDITIONAL native row is relabelled unconditional by this pilot. The DigestDecode lower condition now has a complete local leaf witness once the final revised-reference quartet is checked; U03 parent contracts are still absent. U03 encoders retain DigestEncodeCanonical, U05 retains DigestEncodeRaw/Canonical plus TransferEncode and WithdrawalEncode, and their verified caller chains are not built. The cohort-only U03/U05 equations in NCP_ModelDischarge have no such model hypotheses; that distinction must remain visible.

Actual frozen signatures: afterstate and ASF8 encoders return fixed arrays (688/1880 bytes) in Result; live/late encoders mutate caller slices and return Result<Unit,error>. The Vec shape probe is additional machinery coverage, not evidence that ASF8 itself returns Vec.

## Final per-level native timings

These totals include compilation, verification and matched controls; failures are not promoted to passes. Lean/extraction times remain separately in their receipts.

| Level | Receipts | Total wall s | Peak RSS KiB | Status |
|---|---|---:|---:|---|
| DigestDecode | NCP_K038, NCP_K039, NCP_K040, NCP_K041 | 23.671 | 661960 | local checks with controls; exact scope in bridge report |
| Canonicality | NCP_K042, NCP_K043, NCP_K044, NCP_K045 | 23.947 | 584704 | local checks with controls; exact scope in bridge report |
| Exact8/32 | NCP_K058, NCP_K059, NCP_K060, NCP_K061, NCP_K062, NCP_K063, NCP_K064, NCP_K065 | 50.633 | 693336 | local checks with controls; exact scope in bridge report |
| ValidatorTimeout | NCP_K066 | 98.878 | 6531304 | OPEN |
| FrontierOneStep | NCP_K068, NCP_K069 | 34.024 | 984764 | local checks with controls; exact scope in bridge report |
| DigestEncode | NCP_K070 | 4.673 | 531488 | OPEN |

All listed swaps are0. Full target/argv, exit status, wall/RSS/swap, dirty source revision/hash, dependency fingerprint and axiom outputs are preserved in receipts and NCP_ATTEMPTS.jsonl. No full frozen-release replay or source-to-ELF claim.

Final budget: **70/70 Kani,60/60 charged Lean slots (59 actual Lean invocations),4 extraction scopes**. No more proof launches. NCP_VALIDATION.json passes; all496 frozen source files match after removing only inserted cfg instrumentation; all586 imported cache files retain their hashes;219 resolved Aeneas objects are pinned. No own prover remains; private cache retained. Native source-to-ELF/runtime/SDK assumptions and the deployed security target remain unchanged and unestablished.
