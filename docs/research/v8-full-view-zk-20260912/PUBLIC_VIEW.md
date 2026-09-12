# Public view and chronology

## Observer view

The observer receives:

- the full public statement, proposed afterstate and allowed application
  outputs, including identifiers, roots, nullifiers, account-envelope fields,
  payer/account identities and visible lengths/statuses;
- every serialized proof byte: 697 canonical QM31 fields, C1/C2 roots,
  research nonces, 22 paired opening records, shared salts and both
  authentication frontiers;
- all transcript-derived data publicly reconstructible from those bytes;
- the observer's own adaptive oracle inputs and full 256-bit answers;
- publication, retry/abort and lifecycle events that the actual caller exposes.

Private seeds, undisclosed masks/tables, private prover hash inputs and the
honest prover's complete internal oracle log are not direct view fields.
Actor labels, not domain prefixes, determine visibility. Later public values
may still reveal information about private state; this definition does not
claim otherwise.

The proof-account public key is provisionally the public attempt/mask nonce
for the intended deployed adapter. P0/P8 must still authenticate its exact
location and framing in the generated application envelope.

## Fixed serialization partition

| QM31 indices | Count | Content |
|---|---:|---|
| 0..1 | 1 | initial masking claim |
| 1..271 | 270 | ten semantic rounds |
| 271..358 | 87 | three point rows × 29 columns |
| 358..359 | 1 | inactive weighted sum |
| 359..417 | 58 | two sequential component OOD vectors |
| 417..441 | 24 | four relation rounds |
| 441..697 | 256 | final coefficients |

Roots are 26 bytes each. Each q22 record is 621 bytes: 403 C1 bytes, 186 C2
bytes and one 32-byte salt shared by both trees. Each frontier is at most
296×26 bytes. The maximum body is 40,282 bytes.

## Computation chronology

1. Attempt context, private masks/salts, masked C1, then C1 root.
2. Lambda/chi, C2 helpers/masks, then C2 root.
3. Initial claim, ten semantic rounds/challenges and three point rows.
4. Two bounded sequential distinct OOD samples and component answers.
5. Gamma, image/ordinary relation, first relation round and fold challenge.
6. Final256, q22 derivation, paired C1/C2 disclosures with shared salts and
   both frontiers.
7. Query injection, remaining relation rounds, canonical serialization and
   externally visible terminal status.

Serialization order is not computation order. A simulator must preserve this
chronology and one coherent oracle/cache; it cannot overwrite an earlier
answer or condition away failed attempts.
