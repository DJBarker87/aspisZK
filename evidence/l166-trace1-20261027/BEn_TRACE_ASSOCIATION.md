# Extracted syntax and the trace trust boundary

`BEn_ExtractedTrace.native`, documentation marker `D188_TRACE_BOUNDARY`, is
THE single native-attribution point. It uses the owner-approved D188 reading
in SECURITY-CONTRACT-20261021.md, amendment 2026-10-27 item 2. The trust item
is cited here, not extended by a new Lean axiom or a new caller premise.

The term instrumented is the existing Port9OR_Batch.code reification of
Port3_NativeBatchBody.verifier.candidate.batch_merkle. Port9OR_Batch.source
and its child source lemmas check erasure. Trace attribution is NOT inferred
from that erased equality: instrumentation retains the monadic read nodes
before executing their continuations. We reuse the already present syntax:

| Extracted term/cut | Instrumented syntax |
| --- | --- |
| batch_merkle Prepared reads | BEn_ExtractedSlots.body / Port9OR_Batch.code |
| batch_merkle_values sequential scratch-threaded trees | Port9OR_Batch.values |
| batch_tree header / bounded reached loop | Port9OR_BatchTree.code |
| batch_tree_loop.body leaf before duplicate comparison | Port9OR_BatchStep.body |
| leaf digest boundary | Port4B_LeafCode.code |
| installed P6 binary/tail verifier | Port9OR_P6Verify.code |
| actual digest wrapper, hashv then toBytes | SdkC_Source.digestCode |
| pending-before-return recorder | BEl_PartialRecorder.run |

Port4B's scratch induction and P6 installation are imported unchanged.
BEn_ExtractedSlots.parent checks that the projected operand form is literally
the same batch parent, without constructing an independently chosen Prepared.
Its current/stage maps retain the exact installed error mappings and ordinals.
BEn_LocalAssociation.observation covers BOTH AcceptedPath and RejectedPrefix
for every state, history, backend, slot and operand, including failed reads.
Neither success nor the desired association is in its admission predicate.

This does not close D188-P2's retired tx1 semantic/preparation/query/finish
association rows, P7 binary binding, or joint real-byte non-vacuity. Those are
separate ledger entries. No trust guarantee is claimed for non-extracted code.

Current shipped-cut provenance: BEn_SHIPPED_SOURCE_CHECK.json rechecks all13
exact BEm source cuts (digest/leaf/parent/opening/slot/keys/sort/batch bodies,
constants and verifier entry) by literal body presence and SHA-256. These
checks are source provenance, not a source-to-ELF proof or a fresh extraction.
The inherited three ELF pins remain unmeasured here. The D188-P2 retained
transport qualifications are not relabelled as part of L166's local law.
