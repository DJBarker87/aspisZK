# Validator root closed

Slice S: **97/97 rows, 129/129 internal edges, 7/7 roots CLOSED**, conditional on the named root domains and trust rows. The deployed 100-bit per-attempt target remains not established.

The new root is `programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer` (TX2:226). **uses RuntimeMemcmp (ac), ADDED trust**. Lead adopted, pending owner confirmation. If the owner rejects that row, this scanner root is OPEN and slice S returns to6/7 roots. No ordering, sign, timing or universal-length runtime law is claimed.

Exactly what is proved:

(a) `NFJ_Scanner.result_state_effects` is the MODEL theorem, for every immutable input slice and external state:

```lean
theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State)
    (reply : List U8 → List U8 → Int)
    (runtimeMemcmp : NFJ_Comparison.RuntimeMemcmp reply) :
    (run reply bytes,state,([] : List Unit)) =
    (AspisR1.JHf_Scan.source bytes,state,[])
```

`run` consumes the actual extracted decoder and encoder, including every Result/error; it uses `NFH_ComparisonDomain.complete688 reply` for comparison. `NFJ_Comparison.same_buffer_lengths` proves BOTH reached encoded/header lengths688, from the successful fixed-array encoder carrier and the scanner58295-byte length gate. `nativeEqualityBridge` uses `complete688_on_domain` on those SAME lists; `completion` applies `complete688_association` under the explicitly retained688-only runtime law. No688-only law is passed as a universal native association. Off-domain completion is mathematical and receives no native credit. `slot_zero_iff` relates both branches to exactly the slot's zero observation.

(b) The native link is the ruling-(y) HYBRID certificate, not a single kernel theorem from Rust source. NFD_K134..150 supply the existing length/header/decode/Box/tag/encoder/suffix cuts and controls. NFJ_K003 passes the local-record SAME-buffer/688/slot/reply/branch forwarding cut; K004..010 matched mutations fail. K013/014 pass/fail exact header range identity. K011/012 pass/fail copy fidelity with the exact KMX mitigation. NFH_'s hash-checked ELF wrapper/callsite evidence associates the comparison with sol_memcmp_ at0x1749d0, relocation0x1749e8, and the same result slot. NFJ_validate replays those unchanged gates and checks exact source/cut/record/Result/frame/ordered effects and CLOSED child claims. The three previously unissued edges and external:TX2:226:3..12 now have explicit certificates in NFJ_LEDGER_DELTA.json. No inner callee-domain, bridge or physical hypothesis remains.

(c) Retained conditions: the scanner's own PacketDomain and PhysicalInterpretation, approved library/Allocator/ABI interpretation, RuntimePersistence where used by the enclosing two-transaction game, and P6/D188 composition transport (option A RECLASSIFICATION, never removal). RuntimeMemcmp supplies normal runtime return into the supplied i32 slot, zero-iff-equal for the SAME two688-byte readable ranges, no other observable effect. Runtime abort is terminal, not a returned denial. This is ADDED runtime trust. There is no (ab) use in the scanner; emit_result retains its inherited RuntimeReturnData(ab) use. No cryptographic, privacy, two-transaction or per-attempt target is weakened.

NFJ_VALIDATION.json/.log is the additive replay result. NFJ_TESTS.log records inherited and new mutation tests. NFJ_L003 compiles the final model theorem; NFJ_L001 compiles the five domain/completion lemmas, all with exact standard-axiom prints. L002 is an excluded tag-lemma elaboration failure (its sorryAx diagnostic earns no credit). The final raw axiom audit and eight fixtures are recorded separately in NFJ_AUDIT.json; ordinary #print output is summary-based until checked against that walk. This is focused cached-cohort work, not a cold release rebuild or headline closure.
