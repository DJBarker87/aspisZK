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

## Every stage-2 account and its guards

Let c=4 for genesis/same-page, c=5 for rollover. Pool layout
`P/pair_forest.rs:1217–1318` demands exactly c+8 accounts for transfer and
c+13 for withdrawal under `r1-split-checkpoint`, and all outer keys unique
(:1310–1311). Master/checkpoint/lane are outer 0/1/2; page is 3, with next
page 4 on rollover; marker c, payer c+1, System c+2, registry c+3, entry c+4,
verifier c+5, proof c+6. Withdrawal token range c+7..c+12 is
`[mint,vault,destination,vault_authority,token_program]`; the verifier checkpoint
is appended at c+7 (transfer) or c+12 (withdrawal). The closure arguments at
:1731–1748 select precisely these accounts.

| Nested index | Outer index | Authentication and use |
|---|---|---|
| 0 proof | c+6 | dispatch :92–114: non-writable/non-signer/non-executable, distinct from verifier and verifier checkpoint; owner intentionally unrestricted on R1. V:688 and :1007 enforce read-only and exact buffer scan (:779–805). |
| 1 master | 0 | `pair_forest.rs:430–449`: Pool owner/flags, exact canonical decode, identity.pool=key, stored-bump master PDA bound to mint. dispatch :229–240 repeats owner/non-signer/non-executable. V:690,703–725 independently checks read-only, identity, all-eight-lane mask and PDA, then release policy. |
| 2 historical Pool checkpoint | 1 | `pair_forest.rs:2193–2221`: Pool owner/flags, decode, master link, stored-bump PDA using sequence; request identity guards :1357–1379 bind domain, sequence, global anchor. V:691,733–748 repeats. This is not the verifier checkpoint. |
| 3 selected lane | 2 | `pair_forest.rs:1447–1469`, :500–533 (or source-invariant :546): Pool owner, writable outer lane, no signature, canonical image/PDA/master/lane ID. Selected ID is nullifier-derived :1650–1654. V:692,749–766 independently checks its read-only privilege and lane/master/PDA. |
| 4 registry | c+3 | dispatch :204–218 calls policy authentication; `registry.rs:161–258`: exact pair, registry-owned read-only/non-executable/non-signer, PDA bound to pool, authority/policy/immutable status, no pause. V:535–667 reauthenticates the immutable release configuration (see R15 read audit). |
| 5 release entry | c+4 | same helper: registry owner/flags, PDA bound to pool/profile/release, selected verifier/version/policy equality, Active status and activation/retirement window. V rechecks release certificate; immutable-deployment policy uses `registry.rs:273` branch. |
| 6 verifier checkpoint | c+7 / c+12 | dispatch :99–113 checks selected-verifier owner, read-only/non-signer/non-executable and proof/verifier distinctness; :128–142 excludes master/historical checkpoint/lane/registry aliases. V:689 and :210–221 enforce exact S2 checkpoint size and owner. Core checks digests/provenance per R15. |

`P/pair_forest_dispatch.rs:76–86` requires the selected verifier key,
executable=true, non-signer/read-only and supported loader owner; :219–226
checks the authenticated selection and expected loader. This executable
AccountInfo is the **eighth info**, not an eighth instruction meta.
`:317–341` creates seven `new_readonly(key,false)` metas in the table order;
`:348–364` builds the matching infos and inserts the verifier checkpoint
immediately before the executable. The infos are cloned handles to original
account storage, not replacement buffers. `:365–366` clears return data and
invokes the selected program. The lane's outer write privilege is demoted
for CPI. No Pool signer seeds are supplied to this verifier CPI.

The marker, payer, System program, history pages and five custody accounts
are absent from the verifier metas and infos. They cannot be substituted for
stage-2 inputs by the layout. P2 still supplies actual runtime owner/privilege,
key-to-storage, borrow, instruction-index and CPI demotion enforcement.

## Reconstruction and settlement, both variants

The Pool constructs the common full statement at `P/pair_forest.rs:1473–1502`;
V constructs it at :810–826 from its independently authenticated records.
The field equality map is exhaustive:

| Full statement field | Pool | Verifier |
|---|---|---|
| master/checkpoint/selected_lane account keys | corresponding AccountInfo.key.to_bytes | authenticated copies of those same keys |
| output_lane | nullifier-derived output_lane | authenticated selected_lane.lane_id, checked equal derived ID |
| checkpoint_sequence/historical_global_anchor | decoded checkpoint sequence/global_root | same decoded checkpoint fields |
| live_snapshot.pool | master key | master key |
| live_snapshot.deployment_domain | master.identity.deployment_domain | same identity field |
| live_snapshot.sequence/next_pair_index | lane.tree.next_leaf_index twice | same lane field twice |
| live_snapshot.current_root/frontier | lane.tree.root/frontier | same lane fields |
| candidate_afterstate | authenticated ASR8 result.verified_afterstate | canonical proof prefix, scanned V:779–805 |
| entire variant/public | match request.public at Pool :1548–1555 | match same request.public at V:879–885 |

The last two rows require the accepted-return/proof binding, not merely equal
account keys. V:923–941 emits candidate and kind from its validated statement;
Pool dispatch :367–381 requires selected return program, exact ASR8 length and
decoding. Pool :1750–1760 validates against its reconstructed statement; the
frozen candidate's direct-result feature instead uses :1567–1588, checking
kind, master, selected lane, lane ID, nullifier and checked next-index increment.
`next_pair_forest_lane_v1` (:1382–1408) checks inactive frontier entries.
Transfer copies the entire payment record including both commitments. Withdrawal
copies amount, destination and change; there is no destination in transfer.
The two variants are distinct statements, not equal to one another.

Historical checkpoints are intentionally retained; “stale” does not mean
“not latest” (`pair_forest.rs:2190–2192`). An anchor inconsistent with the
supplied retained checkpoint rejects (:1357–1379). A stale *live lane* relative
to an earlier stage-1 proof is detected by reconstructed-public/checkpoint
binding in the verifier, subject to the hash/provenance premises in R15/R9.

The Pool reserves the nullifier marker before verifier CPI (:1711–1729).
For withdrawal it first plans custody using public destination/amount and
hints (:1692–1707), then after verification invokes the token transfer and
checks the exact custody delta (:1785–1795). Only then does it copy the new
lane image, append/write the selected history page and consume the marker
(:1798–1818). Transfer skips token CPI. Failure rollback of the earlier
System CPI remains runtime P2; native no-CPI tests do not establish rollback.
Neither path writes the master, retained checkpoint, registry, release entry,
proof or verifier checkpoint during settlement. No keys are created or removed
by this audit/test job.
