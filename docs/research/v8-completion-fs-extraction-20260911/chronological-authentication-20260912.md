# Chronological source authentication — 2026-09-12

`lean/SameBodyChronologicalAuthentication.lean` executes the bounded C1 and
C2 builders from one empty shared oracle, retains their actual commitment
cuts, and continues from the resulting transcript with the replayable
source's live q22 schedule and selected same-body Merkle verifier.

On success, `successful_authentication_inputs` constructs rather than assumes:

- answer consistency for both chronological commitment prefixes;
- inclusion of both prefixes in the same final opening log;
- the parsed same-body `SuccessfulMerkleRun`, both root equalities, and exact
  leaf/node call inclusion in that same final log.

Early failure, source/sampler failure and selected parser/root/Merkle aborts
remain failures of the actual composed script. The theorem does not assume
opening equality or complete verifier/payment acceptance.

The next `Prepared` composition was reduced to a mechanical endpoint: its
wire and trace are forced equal to this constructed Merkle run, hence its
call inclusion is available. The first monolithic proof attempt then hit a
Lean definitional-equality heartbeat limit at the final application of the
already proved authenticated-scalar theorem. That endpoint is not promoted
here; it should be completed in a smaller follow-up leaf.

## Focused evidence

- Base revision: `d1a195ec9d29d8ebbf3502880e59b65edcedf45d`
- Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
- `MemoryHigh=8G`, `MemoryMax=9G`, `MemorySwapMax=0`, `-j1 -M8192`
- Exit: 0
- Wall time: 2.81 seconds
- Peak RSS: 6,744,572 KiB
- Swap: 0
- Source SHA-256:
  `c82b903d2ab50ea045aea9813fe7f9e819eb5e55fd8c3334a000096568d4f09c`
- Olean SHA-256:
  `92ebe19fc4fac3d62e2f7bda7e1a4abd6fb58efe9c171b77017c4e4ebef87de2`
- Axioms: `propext`, `Classical.choice`, `Quot.sound`

