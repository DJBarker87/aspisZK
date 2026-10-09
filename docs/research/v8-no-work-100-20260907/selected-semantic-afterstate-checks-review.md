# Selected afterstate: wrapper checks and actual table bindings

Status: **V2 GREEN and frozen**; V1 retained as a failed diagnostic.
Import `experiments/SelectedSemanticAfterstateChecksV2.lean`, namespace
`AspisV8.SelectedSemanticAfterstateChecks`. Eight standard-only axioms
audits. V2 source SHA256:
`43c76b19200f6ccbc554842eee89fb56f86f69de20d7f4c127fa605a0dcebc92`.
Working source parent: `8761cd89ab7ccea779ef4a9f86fa415d670bd16d`.
Only import: frozen green `SelectedSemanticAppendResidualsV2`, source
`a175259706c5773d3af57b1c6d7b6ab66d0d288085fadf6b131b3ceae248d5dd`,
olean `50773ac7785e3ca55db49e17f8299d0b30bb6bf7c4b40a139030b5aa911c2230`.
No new dependency/cache registration is requested.

V1 (`selected-semantic-afterstate-checks-nuc-v1`) exited1 after3.12s,
peak6,693,480KiB, zero swaps. Only `digest_at_carry` failed: the final
`if row=16*(33+carry)+11` did not reduce through the named local `row`.
V2 supplies `rowExact := rfl`, takes `if_pos rowExact`, then transports
the frontier lookup by `Fin.ext rfl`, so proof witnesses are immaterial.
The statements, eight audits and all caps are unchanged. V1's transitive
`sorryAx` reports are diagnostic only, never green proof evidence.

Retained local V1 source/log/manifest triplet:

- `selected-semantic-afterstate-checks-nuc-v1-source.txt` (same as V1 Lean):
  `2c0b4c53e50a08035776869d864da53873c7c63f7733f95b97c6c358fc950c56`;
- `selected-semantic-afterstate-checks-nuc-v1.log`:
  `16a6f9d31eddc67f87c9d1b4729d4e7cc62c4095adfa60e234b020e05885858b`;
- `selected-semantic-afterstate-checks-nuc-v1-manifest.json`:
  `82d7f54f71e1f3e840a5c2606067a2625625d88f3a5a2bdeaae44baf6b47fba0`.

V2 (`selected-semantic-afterstate-checks-v2-nuc-v1`) exited0, wall3.33s,
peak6,726,728KiB, zero swaps. All eight audits contain only `propext`,
`Classical.choice`, and/or `Quot.sound`; no `sorryAx` or compiler errors.
The1061-entry pre/postflight manifests passed and provenance was unchanged.
V1 had1059 initial entries and no successful postflight. The later manifest
addition does not require replaying or changing the prior failed artifact.

Exact green artifact hashes:

- source/snapshot `43c76b19200f6ccbc554842eee89fb56f86f69de20d7f4c127fa605a0dcebc92`;
- log `988226fc9da7bbb0329b0483bee278484734840fa468ef97ef7715c35c587b5f`;
- manifest `58964cb4c99c7a49787f626d5ec3de822aabdebf65ba8f1fd0be85d5630fcd86`;
- olean `d5e94f8d0ef9b0fa13e049eb399fce0d9605e91e64536dc597e8b7782a812b1f`.

The actual NUC runner used Lean4.32.0 `-j1 -M9500`,
High8GiB/Max10GiB/Swap0/CPU200%, reached over Tailscale. Runner bootstrap
parent remains `289d7356c78a4cd493fe61a54f9548f2a0c11298`, distinct from
the working source parent above; borrowed pin remains
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. Runner SHA256 is
`5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.
No cold cache closure or proof replay occurred during evidence closeout.

## Exact field classification

The four public comparisons below are executed by
`pair_forest_semantic_terminal.rs::validate_transition` before openings are
used in `evaluate_components`. They are not stochastic semantic claims.
The remaining two fields are actual table equations, not public comparisons.

| `AfterstateChecks` field | Actual source and authority |
| --- | --- |
| `sequenceIndex` | `validate_transition` rejects `sequence != next_pair_index`; `live_snapshot_box` independently constructs both from the selected account's `tree.next_leaf_index` in complete ASQ8 |
| `notFull` | terminal rejects index≥`POOL_V1_PAIR_CAPACITY`; snapshot byte decoder also rejects it; Pool spend-layout planning rejects a full account |
| `increment` | terminal and late-statement decoder compare `checked_add(1)` to candidate index; complete ASQ8 reconstruction and Pool result checks repeat this check |
| `staticFrontier` | terminal loops over20 levels, skips only `level==carry && carry<20`, and compares every other candidate slot to literal empty root or source frontier |
| `carryBinding` | digest residual at `16*(33+carry)+11`, only if carry<20; not checked by account authentication or candidate canonicality |
| `rootBinding` | digest residual at859; not a public/account comparison or independent recomputation by the Pool |

The source carry is `min(index.trailing_ones(),20)`. The selected Lean carry
is `SelectedAppendAfterstate.carryScan index.testBit 20`. This leaf does not
silently identify those implementations.

`SourceComparisons pub sequence nextIndex rustCarry` preserves the exact
static skip condition and expected frontier expression above. It records
these source comparisons as explicit hypotheses; it does not define or
claim verifier acceptance. Pool/deployment comparison, canonical bytes,
account authority and the source extraction supplying these hypotheses
are outside that predicate. Integer successor in the model is exact Nat
successor: translating Rust `checked_add` requires its successful branch
(index<2^20 makes overflow irrelevant), not a field equality modulo M31.

## New nontrivial deterministic step

`sibling_sum_at_eleven` proves that every sibling-digest summand vanishes
at a row congruent to11 modulo16. `digest_at_root` isolates row859; the
guard carry<20 places all dynamic carry rows at539..843, so no root/carry
cancellation is possible. `digest_at_carry` isolates the actual carry row;
all other public rows427/475/523/907 and root859 are distinct. The complete
sum is retained and rewritten before simplification.

`dynamic_bindings` derives both missing table equations directly from
`RowsVanish pub t`. `afterstate_checks` combines these with the four literal
comparisons and explicit
`rustCarry = SelectedAppendAfterstate.carryIndex pub.appendIndex` to build
the original `AfterstateChecks` record. The dependent
`semantic_transfer_transition` consumes the previous append/output/payment
endpoint, on the same `semanticTable candidate`. No `AppendResiduals`,
`AfterstateChecks`, checked witness or decoder success is supplied.

All proofs keep depth200. No generated large enumeration, native field
evaluation, new V7 closure or broad build was used.

## Precise counterexample boundary

`source_comparisons_do_not_force_table_binding` constructs an index-zero
proposal with nextIndex1, literal empty frontier, and candidate root `e0`.
The four comparisons hold, and a symbolic use of `carry_scan_spec` proves
the exact modeled carry is zero. Nevertheless the zero table cannot satisfy
rootBinding: its first limb would require `0-1=0`.

This is a counterexample to *public comparisons imply table equations*,
not to accepted proof verification. `RowsVanish` and the cryptographic check
are absent. The constructed proposal's unrelated payment fields are dummy
values; no full canonical payment/ASQ8 acceptance is claimed. Authenticating
an independently valid index-zero source cannot by itself constrain an
unrelated table or the proposed new root.

## Actual account path versus bare research callback

The bare `performance_verifier::verify` decodes public/late bytes but has
no AccountInfo, owner/PDA, registry or return-data authority inputs.
`verify_payment` accepts typed objects; its comment requires the complete
wrapper's checks but its signature cannot enforce that contract. The local
`performance-sbf` benchmark checks only three read-only accounts and a
32-byte instruction before passing their bytes through. Its success alone
does not authenticate a Pool snapshot.

The complete research path is different, and is not accused of this gap:

1. `complete-sbf/lib.rs` uses `process_v7_pair_forest_asq8_instruction`.
   `complete-integration.patch` replaces proof-length/callback/profile hooks,
   not account reconstruction.
2. `authenticate_asq8_accounts_v1` checks exact account count, owners,
   readonly/non-signer/non-executable privileges, distinct keys, canonical
   master/checkpoint/lane data, PDA/master bindings and selected lane. Its
   `live_snapshot_box` copies index/root/frontier from that same lane.
3. `scan_asq8_proof_v1` canonically decodes the proof-carried688-byte
   candidate; it is still a proposed afterstate, not authenticated truth.
   `asq8_common_box_v1` combines it with the account-derived snapshot.
4. The complete statement digest and verifier/proof-account identities feed
   `complete_binding::bind_attempt` before the C1 root. Pool/deployment,
   asset, checkpoint/anchor and selected-lane checks constrain the public
   inputs. Successful hashing does not alone prove collision resistance.
5. The Pool independently checks its own program identity, account owners
   and PDAs, selected lane, retained checkpoint/anchor, asset and spend
   layout. Dispatch authenticates registry profile/release/verifier and
   proof-account ownership; CPI receives those same accounts read-only.
   Immediate return data must have the selected program ID and exact
   canonical ASR8 shape. The Pool checks result account/nullifier/kind/index
   echoes, then writes the selected lane/history/nullifier marker only
   after the result and settlement checks.

Relevant source functions are in
`programs/aspis-verifier/src/v7_pair_forest_dispatch.rs` (account constructor
at409, authentication424, candidate scan544, reconstruction621),
`programs/aspis-pool/src/pair_forest.rs` (request/account checks1096,
result application1154, terminal flow1384), and
`programs/aspis-pool/src/pair_forest_dispatch.rs` (registry planning119,
immediate return authentication after CPI). Feature-selected invariant
decoders still rely on the Pool-owned state invariant; this is not newly
proved by the selected semantic table.

## Exact V7 reuse and missing source theorem

`V7EightLaneCompactDispatch.authenticated_result_gives_identical_semantic_reconstruction`
is the existing pure transport theorem: given one exact shared account
snapshot and `ResultAuthenticates`, both sides reconstruct the same semantic
object. It explicitly leaves byte/PDA/CPI refinement outside its theorem.
`V7PairCallerLiveSnapshotGate.bound_snapshot_transports_exact_transition`
likewise requires the proof-bound/account-derived equality; its historical
comment that the then-current caller omitted the snapshot is not a claim
about the later ASQ8 complete wrapper inspected here. Its cursor-only
counterexample remains a valid warning, not a current integration finding.

The first still-missing authenticated-source theorem must connect successful
actual ASQ8 account parsing/reconstruction (and the immediate Pool result)
to this selected `Public` value and the same account sequence/index/frontier.
`Public` presently has no pool/deployment/sequence/current-root/account fields.
Merely adding an `Authenticated` predicate whose definition is the desired
equality would not discharge that source obligation. Existing V7
`CompactTransferAccepted` additionally assumes the transfer relation and
input backing; it cannot be imported as a decoder or witness proof here.

This leaf therefore closes the real missing row projections while retaining
source comparison provenance, Rust carry correspondence, account/runtime
refinement, the accepted-to-same-table extraction premise, deployed
Poseidon faithfulness, and historical membership as explicit boundaries.

## Inspected source pins (read-only)

```text
performance_verifier.rs bf8a24c42c0d5493d2259fa19a70b1a8bf4ba168f661b71cfed6d33c70eebfbc
complete_callback.rs aaf776171df5bbab9e3f18339990acb857092b59be9d84d7f5fd948254394419
complete_binding.rs d35d46ac4b0128de04a333377e1d6dc801de313dce6111e3e820d3384cd9a360
complete-integration.patch 677e9ff8ae0c09e2ecc9b09a04702323726fb632f7eaa6156e76e5eccf39301b
programs/aspis-verifier/src/v7_pair_forest_dispatch.rs 4577c435a5c41a147331ca7d42b65053e181d58dca1b4322ef96b48c85babf77
programs/aspis-pool/src/pair_forest.rs d96b352bae081a72d6e887759a356674598e0bf3a177c8d103885f02bc344c30
programs/aspis-pool/src/pair_forest_dispatch.rs 7e45910a3d64e328dc234ede290119770e898bcb48f277d978219740ec891514
pair_tree_profile.rs 8a7a4c7bdd3fe0ecd14d6fc920182be434ab92536924de22d269d906be3387b2
pair_forest_semantic_terminal.rs efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58
V7EightLaneCompactDispatch.lean 41bbb65b7eb6344801cea6659dc5eb5ec221c2141e07f85bffb1fbb0962b52ee
V7PairCallerLiveSnapshotGate.lean 9fc74c036b4f692114288585a8d3daff3e53f6c8282280133375d8c82c5abb3d
```

## Read-only evidence check and publication

From the research worktree:

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_selected_semantic_afterstate_checks.py --check-recorded
```

The auditor validates the preceding append receipt, both current attempts,
exact source/log/manifest/resource/axioms facts, six imported retained green
source/olean pairs, and the inspected source pins above. Native package
artifacts remain a pinned-cache boundary, not a claim of cold recompilation.
The JSON binds this report and script. Sources/snapshots/logs/manifests/JSON
are mandatory; ignored local oleans are verified only when present. The
green olean was copied and verified locally, but is not published.

Publication is eleven files: both Lean versions, this report, the new audit
script and `selected-semantic-afterstate-checks-evidence.json`, plus the
log/manifest/source snapshot for each of the two named attempt tags.
Existing green sources, unrelated untracked files, production, Git index,
commits and ignored cache payloads were not changed by this task.
