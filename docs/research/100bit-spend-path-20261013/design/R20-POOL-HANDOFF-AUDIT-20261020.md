# R20 Pool CPI handoff audit (2026-10-20)

Scope: branch `codex/cx-r20-pool-20261020`; production Pool and frozen verifier
unchanged. Source revision and whole input hashes are in
`evidence/r20-pool-handoff-20261020/`. This is an AccountInfo source audit under
runtime premise P2, following the R15 read/write audits. It does not instantiate
`BoundaryStatements.R20` (`lean/R1FinalSoundness.lean:53`) merely by naming it.
All byte intervals below are half-open. P abbreviates `programs/aspis-pool/src/`,
S `crates/aspis-statement/src/pool_v1/`, V
`programs/r1-cost-probe/src/r1_pool_adapter.rs`.

## Instruction admission and suffix

`P/processor.rs:2412` clears return data and, on Solana, requires top-level
invocation (:2424). ASQ8 dispatch (:2471–2483) obtains Clock and Rent and calls
`process_pair_forest_terminal_v1`. Its selected verifier closure is
`P/pair_forest.rs:1823–1841`. The optional ASF8 audit route (:2490) is separate;
it is not the admitted compact R1 route.

`P/pair_forest.rs:139–155` subtracts exactly four, failing below four bytes,
then splits and reads `[current_page,next_page,vault_authority,vault_token_account]`.
The body goes to the exact 320-byte decoder (:1642–1643). Thus the Pool input
is 324 bytes. A suffix is not itself authorization: current-page bump is
checked against the page PDA at :1234–1241 or :1245–1262; rollover next page
at :1268–1280; unused next byte must be zero (:1288). Transfer vault bytes
must both be zero (:1669). Withdrawal vault bytes feed custody PDA planning
(:1693–1705). The source calls these B4 hints; the marker optimization is B1.

## Every byte of the CPI data

The Pool decodes the body then re-encodes the same typed request
`P/pair_forest_dispatch.rs:161–164`; it does not forward the suffix. Instruction
construction at :342–346 sets `data = plan.request_bytes`. The encoder is
`S/pair_forest_terminal.rs:432–464`, decoder :466–523. Identity arrays must
be nonzero; exact headers, variant-specific payment validation, canonical
M31 words and reserved zero bytes prevent alternate accepted encodings.

| CPI interval | Contents / origin |
|---|---|
| 0..4 | ASCII ASQ8 |
| 4 | terminal version 1 |
| 5 | transition kind, PrivateTransfer=1 or Withdrawal=2 (historical_anchor.rs enum) |
| 6 | digest encoding version |
| 7 | zero reserve |
| 8..40 | request.verifier_profile |
| 40..72 | request.verifier_release |
| 72..104 | request.pool_program, required equal runtime Pool program |
| 104..108 | ASCP (transfer) / ASWP (withdrawal) |
| 108 | payment version 1 |
| 109 | same payment transition kind |
| 110 | digest encoding version |
| 111 | zero reserve |
| 112..144 | public.pool |
| 144..176 | public.deployment_domain |
| 176..184 | public.anchor_sequence LE64 |
| 184..216 | public.anchor_root, eight canonical LE32 M31 limbs |
| 216..248 | public.nullifier, same digest encoding |
| 248..252 | public.asset_id LE32 canonical M31 |
| 252..256 | transfer zero fee/reserve; withdrawal amount LE32 |
| 256..288 | transfer recipient_commitment digest; withdrawal destination public key |
| 288..320 | change_commitment digest |

Payment layout constants are `S/payment_relation.rs:34–43`; encoders
:258–337 and header checks :340–365. No candidate afterstate occurs in ASQ8.
It is separately carried in the proof account and bound by the verifier.
