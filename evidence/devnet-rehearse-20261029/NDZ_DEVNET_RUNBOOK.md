# NDZ devnet runbook — review only; no public write performed

The lead reviews this runbook and evidence before a separate public writer runs
steps 2–3. This worker stops after local rehearsal and runbook delivery. Owner
approval of deployment did not lift this worker's explicit public-write ban.
No command below migrates or rewires the old Pool state.

## Fixed inputs and authority

Release ELF: 1,563,728 bytes, SHA256
`63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`;
frozen source `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.

New verifier: `CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ`.
Expected loader-v3 ProgramData (public planner derivation): `7GVKbnPt1XkYvnZURDLRKJqC89qbgfqP912hM3aUojRk`.
Retained key: `~/.config/solana/aspis-deploy/NDZ_release-20261029/verifier.json`.
Payer/buffer/upgrade authority:
`CVZJcAv97von8njTJSyLVQ9X33NAKQYbEXFKnAYvst9t`, retained at
`~/.config/solana/aspis-deploy/devnet-payer-20261029.json`.
Both key files were checked mode 0600 and by public key. No secret was copied.
The lead must confirm policy-compliant backup/retention before the public run;
this worker does not assert that a backup of the newly generated key exists.

Unchanged programs: Pool `BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs`,
registry `9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q`,
carrier `3jEFrv5Npn3RmFMW1Cbzq5yEiLdeFB5vbBGmnfoqK9vN`.
The registry program is already immutable; do not redeploy or finalize Pool or
carrier. Only the new verifier is deployed/finalized, and only its fresh Pool's
registry entry is scheduled/activated/frozen.

Configuration is `NDZ_devnet.review-only.json`. It deliberately omits the old
mint/account identities. `key_namespace=NDZ_devnet` creates fresh retained mint,
source, destination, governance, public/checkpoint and selected64 proof keys
inside the durable task key directory. `proof_key_dir` is that same directory.
The proof artifact directories also remain private there. Never replace a
missing key on resume, move keys to an offload directory, or clean this directory.

## Writer environment (already prepared and read-only checked)

Run on this Mac from the assigned worktree. Docker image
`sha256:a5fd19592cef47ad41bf1891997e324febf21a442cc71fac4eaf77877d60562a`
is locally materialized. NDZ_writer.sh pins it, binds the retained keys in place,
uses the same Linux amd64 client and Agave 4.2 CLI as the rehearsal, and enforces
4 GiB memory, zero swap, four CPUs and 256 tasks. The payer mount is read-only;
new task keys are written only to the durable key directory. The worktree mount
is read-only except `NDZ_devnet_receipts/`. No secret is in the image.

Client SHA256:
`77e7e541378baa655ba8ebd47052e67a145807392e03d7ce48d6a4bb13ca8289`.
CLI SHA256:
`b6134ccddcb3456e49c0c15bc028c2902184a8fef6f6e6e665d9f8ae5bea8d10`.
Keygen SHA256:
`c3385c5a56a1656a14dbc97574713e0676c52668ab1af6a6755569d3f5eb3312`.
NDZ_WRITER_READINESS.json records a network-disabled public planner test and
caps. NDZ_WRITER_PROVE_RESULT.json additionally records one fresh offline proof
generated in 39.34 seconds, with 618475520-byte cgroup peak and zero swap; no
devnet key was mounted and no signature was generated. Both retained key identities were checked through the container. If the
image/binaries are missing or hashes differ, stop and rematerialize/review the
public tools before any public write; do not silently rebuild the release ELF.

Set these exact variables (all commands below use this configuration):

```sh
cd /Users/dominic/ZK/.worktrees/cx-devnet-rehearse
E="$PWD/evidence/devnet-rehearse-20261029"
C="$E/NDZ_devnet.review-only.json"
R="$E/NDZ_devnet_receipts"
writer() { bash "$E/NDZ_writer.sh" "$@"; }
```

### 1. Read-only preflight and funding gate

```sh
writer python3 "$E/NDZ_funding_check.py" "$C" "$R/NDZ_FUNDING.json"
```

Expected: correct retained public keys, devnet genesis
`EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG`, absent new verifier address,
exact release ELF hash/length, pinned loaded dependency payloads, immutable
registry deployment, active TxV1, inactive legacy-SBPF deployment ban, `funding_pass: true`, positive headroom. The script derives
current rent quotes for every rehearsed account size, includes a 0.1 SOL fee/retry
reserve, and uses the conservative double-allocation peak bound. The complete
rent/peak/locked figures are recorded below and in NDZ_FUNDING.json.

STOP on any mismatch, unexpected existing verifier, insufficient funds or missing
key. This step sends no signature and requires no rollback. Never airdrop,
transfer SOL or substitute a wallet without a separately reviewed funding step.

### 2. Deploy, byte-verify, finalize the verifier

**First public write. Execute only after lead review.**

```sh
writer python3 scripts/r1_devnet_deploy_paced.py \
  "$C" "$R/NDZ_deploy" verifier
```

Expected sequence is identical to the successful local deployment:

1. Check payer/program key presence, mode and public identity, then genesis.
2. Generate/retain `verifier-deploy-buffer.json`, record its public address and
   fund an ELF+37-byte loader-v3 buffer. Each signed attempt is receipted.
3. Write 900-byte chunks with simulation before submission, at most 60 submitted
   before the finalized wait; expect `1738/1738 repaired` on a new zero buffer.
4. Require complete buffer payload equality with the pinned ELF.
5. Invoke loader-v3 deploy with the retained verifier key, retained buffer,
   `--max-len 1563728 --use-rpc --max-sign-attempts 2`.
6. Require loader Program/ProgramData ownership and tags, correct linked address,
   payload offset 45, exact 1,563,728-byte payload and SHA256. No trimming zeros.
7. Only after byte verification, run `program set-upgrade-authority ... --final`;
   require ProgramData authority Option byte 12 = 0 and unchanged payload.
8. Record final program/rent receipts and require `{"buffers":[]}`.

Expected terminal output: `verifier deployment verified`. The retained buffer
key remains even though its funded buffer has been consumed. The script's receipt
contains all loader-write signatures/metadata, finalization output, ProgramData
address, lamports, hash and empty final inventory.

| Stop point | Recovery before continuing |
| --- | --- |
| Key/genesis/hash check | No public account should have been funded. Inspect; keep keys. |
| Buffer creation/upload/readback failure or SIGINT/SIGTERM | Reconcile every submitted attempt to finalized or expired-unlanded. Script closes the identified payer-controlled buffer to the payer and checks finalized zero balance. Ambiguity stops recovery and retains keys; inspect before any retry. |
| Deployment failure | Same buffer recovery. Check whether Program/ProgramData exists before resuming; do not blindly redeploy. |
| Successful deploy, before finalization | Verifier is still upgradeable by retained payer; its ProgramData rent can be recovered by reviewed loader close. The small 36-byte Program stub rent has no loader-v3 close path and remains a locked budget item. |
| After finalization | Verifier rent is permanently locked. There is no upgrade/close rollback. Keep all keys and proceed only with the exact verified ELF. |

If manual buffer recovery is required after reconciliation, use its exact public
address from `verifier-plan.json`, never `--buffers` to close unrelated accounts:

```sh
# BUFFER is the recorded public buffer address, not a key file or secret.
writer /opt/aspis/cli/solana --url https://api.devnet.solana.com \
  --keypair /Users/dominic/.config/solana/aspis-deploy/devnet-payer-20261029.json \
  --commitment finalized --output json program close "$BUFFER" \
  --authority /Users/dominic/.config/solana/aspis-deploy/devnet-payer-20261029.json \
  --recipient CVZJcAv97von8njTJSyLVQ9X33NAKQYbEXFKnAYvst9t
```

Record finalized close signature, recipient and zero source balance. Before
finalization only, the analogous reviewed Program close refunds ProgramData rent and uses the new verifier
public address and `--bypass-warning`; it is irreversible and must not be run
against any reused dependency or after finalization. The [loader-v3 close path](https://github.com/anza-xyz/agave/blob/v4.2.0/programs/bpf_loader/src/lib.rs#L646-L742) drains ProgramData, not the small Program stub; do not promise a full two-account refund. There is no key-cleanup step.

Exact manual ProgramData recovery command, **only before finalization**, after
checking the new program still has the retained payer as upgrade authority:

```sh
writer /opt/aspis/cli/solana --url https://api.devnet.solana.com \
  --keypair /Users/dominic/.config/solana/aspis-deploy/devnet-payer-20261029.json \
  --commitment finalized --output json program close \
  CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ \
  --authority /Users/dominic/.config/solana/aspis-deploy/devnet-payer-20261029.json \
  --recipient CVZJcAv97von8njTJSyLVQ9X33NAKQYbEXFKnAYvst9t --bypass-warning
```

This closes the new program permanently and refunds ProgramData only; retain its
key and account for the nonrefundable Program stub. It is not part of normal success.

Independently verify after deployment:

```sh
writer python3 "$E/NDZ_VERIFY_PUBLIC.py" "$C" "$R/NDZ_IMMUTABLE.json"
```

Expected: correct verifier/ProgramData link, `immutable: true`, exact ELF length
and release hash. STOP on mismatch. The immutable verifier rent cannot be refunded.

### 3. Fresh registry, fresh Pool and honest TX1/TX2

```sh
writer python3 scripts/r1_devnet_spend.py "$C" "$R/NDZ_spend"
```

The script's exact ordered phases and stop points are:

| Phase / expected receipts | Expected result / stop and recovery point |
| --- | --- |
| mint-create/initialize, source/destination-create/initialize, mint-supply | Fresh retained mint/token keys; supply 2000 base units. Stop on unexpected existing identity or nonfinal receipt. Zero-balance token accounts have SPL CloseAccount recovery via retained governance; mint has no standard close path. |
| registry-initialize | Fresh registry for the future fresh Pool PDA; generation 0, governance authority retained. Its account rent has no demonstrated close instruction. |
| registry-schedule | Exact immutable release program/ProgramData/hash/profile/release stored; activation at confirmed slot +100, minimum delay 20 slots. Stop on any error; retain governance and state. |
| registry-activate | Wait until finalized activation slot; exact entry active, generation 2. Before freeze, governance can pause/retire through normal instructions; this does not refund account rent. |
| registry-freeze | Registry immutable, generation 3, authority zero. Irreversible; no unfreeze or registry-rent recovery. |
| pool-initialize | New master derived from the fresh mint, eight fresh lanes and vault, bound to this immutable registry policy. It occurs after freeze because pool_initialize_after_registry=true. No old Pool state is modified. Pool-owned PDAs have no demonstrated close path. |
| deposit-0/deposit-1, forest-checkpoint | Deposit the two public fixture notes (1000 each); create honest checkpoint. Retain mint/token authority and fixture/proof keys. Do not manufacture Pool state if a step fails. |
| transfer proof + statement uploads (16+1), checkpoint-create, transfer-stage1, transfer-stage2 | Selected64 retained-key client; TX1 and TX2 finalize successfully. Vault=2000, destination=0. Stop on client/metadata/simulation failure; no automatic new proof-key allocation or proof retry after ambiguous failure. |
| transfer-replay, fresh negative checkpoint, mutated-stage1, restore-proof | Replay rejects NullifierAlreadyConsumed (0x41532026), protected accounts unchanged; changed proof rejects InvalidInstructionData with zero checkpoint unchanged; original proof restored. |
| withdrawal uploads (16+1), checkpoint-create, withdrawal-stage1, withdrawal-stage2 | Honest withdrawal TX1/TX2 finalize. Vault=1750, destination=250 base units. |
| withdrawal-replay, fresh negative checkpoint, mutated-stage1, restore-proof | Same exact rejection/no-state-change checks; restored proof. complete.json records both successful spends and all four negative checks. |

Every creation updates rent-ledger.json, including CPI-created PDAs. Every send
records signature, fee, CU, slot, serialized size, error and finalized status.
Do not rerun into a new receipt directory to escape an incomplete transaction.
The script reconciles retained attempt signatures and reuses only validated
finalized receipts. Missing selected64/auxiliary keys cause a hard stop. Retain
all keys and accounts on failure; no broad account/key cleanup is authorized.

Proof/public carrier accounts and verifier checkpoints have no closing instruction
in these unchanged programs; budget their rent as locked. The source token
account is zero after deposits and can later be closed by governance to the
retained payer. The destination still holds 250 tokens: transfer them to a
retained account before any reviewed close. Pool vault assets remain subject to
normal proof-authorized withdrawal; this runbook does not claim a direct refund
or close route for Pool PDAs. No state-account cleanup is part of the rehearsal
or proposed demonstration.

### 4. Read-only chain association and final audit

```sh
writer python3 "$E/NDZ_ASSOCIATE.py" "$C" \
  "$R/NDZ_spend/setup-plan.json" "$R/NDZ_ASSOCIATION.json"
writer /opt/aspis/cli/solana --url https://api.devnet.solana.com \
  --keypair /Users/dominic/.config/solana/aspis-deploy/devnet-payer-20261029.json \
  --output json program show --buffers \
  --buffer-authority CVZJcAv97von8njTJSyLVQ9X33NAKQYbEXFKnAYvst9t \
  > "$R/NDZ_FINAL_BUFFERS.json"
```

Expected: one finalized snapshot links the distinct fresh Pool/mint/policy to
its frozen registry, active exact profile/release entry, new verifier and immutable
ProgramData containing the pinned ELF. Final inventory must be empty. Retain
all signatures, account snapshots and rent/refund receipts. STOP on any mismatch;
never represent the old Pool as migrated. The lead then evaluates the real-devnet
receipts and association against L188 obligation 5. Local receipts alone do not
discharge that obligation.

## Measured rent and funding ledger

All numbers are SOL. Public amounts are finalized read-only rent quotes in
NDZ_FUNDING.json, not a public deployment measurement. Each created local account,
its actual lamports, current devnet quote and close/recovery classification is in
NDZ_RENT_LEDGER.json (28 fixture accounts, two verifier accounts, two closed buffers).

| Item | SOL | Meaning |
| --- | ---: | --- |
| Retained devnet payer | 18.353204080 | Finalized read-only balance |
| Verifier ProgramData | 7.944617080 | Permanently locked on finalization |
| Verifier Program stub | 0.000833120 | Locked; no loader-v3 close path |
| Verifier total | 7.945450200 | Exact proposed permanent verifier rent |
| All fresh fixture accounts | 0.791499560 | Includes governance-controlled SPL accounts |
| Fixture rent budgeted as locked | 0.788522680 | No demonstrated close path in unchanged programs |
| Combined locked budget | 8.733972880 | Verifier plus no-close fixture budget |
| Potentially recoverable SPL rent | 0.002976880 | Source can close now; destination requires token transfer first |
| Fee/retry reserve | 0.100000000 | Above measured normal-route fees |
| Conservative peak reserve | 16.781526200 | Buffer + Program/ProgramData + all fixtures + fee reserve |
| Headroom against payer | 1.571677880 | Positive; funding check passes |
| Measured higher-rent local peak outlay | 11.997749120 | Started with the same 18.353204080 SOL |
| Local workflow fees | 0.027440000 | Includes the deliberate buffer-failure probe |
| Local ending payer | 6.355454960 | Fully reconciled against rent and fees |

The local validator uses the older 6,960-lamport rent rate; devnet currently uses
5,080. Local locked-budget lamports are 11966230560, and potentially
recoverable SPL rent is 4078560 lamports. No token-account cleanup
was executed. The source token balance is zero; the destination holds 250 tokens
in base units and must retain its authority until an approved transfer/close.
The small failure-test buffer returned 141294960 lamports to
`JDBfF4zrTqddwXJsVEFjjMBAx8f5SDHCf8GcCzZikx4R`; close signature `4aBywkMEWjgWx9GkHQZDrqj9pcjuSfuUVB6GjfCkAXFyADGeWZybX19tzAdasjuVdgJhYUBDcFvjejscNnURq3Ef` is local only. Both final
buffers are absent/zero. All keys remain retained.

The conservative public reserve intentionally counts both loader allocations;
the measured loader route reuses buffer funds before allocating ProgramData.
With unchanged fees, the normal public route is estimated at 0.027415 SOL in fees
(the local failure probe adds 0.000025 SOL). These are estimates; rerun step 1
immediately before the separately reviewed public write and stop if funding or
feature/dependency checks fail.
