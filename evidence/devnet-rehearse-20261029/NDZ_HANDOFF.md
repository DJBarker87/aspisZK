# NDZ handoff — local rehearsal PASS; public execution not performed

Established claim: the exact frozen release ELF can run at a fresh verifier address
under the unchanged deployed Pool and registry program IDs. The final local ledger
used the real-ID cloned Pool/registry/carrier programs, deployed the unmodified
1,563,728-byte release through the paced loader-v3 route, verified exact ProgramData
bytes and finalized it. Its fresh registry followed initialize → schedule → activate
→ freeze (generation 3, zero authority); the distinct fresh Pool then initialized.
Both honest transfer and withdrawal TX1/TX2 pairs and all four negative checks passed.
This is an operational identity/execution result, not a new soundness theorem.

Release SHA256: `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`.
Frozen core source: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.
All crates/programs remain identical to that revision. Only scripts/configuration,
policy tests and NDZ evidence changed. Script changes are committed separately.
No push, public transaction, public signed simulation, public airdrop or public
signature submission occurred. The retained devnet payer still had
18.353204080 SOL at finalized slot 516419609.

## Exact local result

RPC `http://127.0.0.1:18995`, genesis `5iQmsmUGNpQzebT1ZGSJX8Jbu8tRJv7RBcCDMMVKrpt`.
Verifier `BWqJ6cr2ZYpg2LaBHacX5vfaZXczVMMcv8u18H7GetMx`, ProgramData `2PU7wFDxL8RtWjUw7dtCchLKEgnrEdYRhFmws6jhhVFK`.
Fresh Pool `3GTDbFNrJgCLUARGELCD4RU7vHmwyNHYYXWhLtM12Z17`, registry `6rv5WyZxEEAqV3jvKFK2bJtk2Phdw1rwfBMWe8nG2LxW`,
entry `AcEtPVNTWj5XiSCMoViRRboackPUJgGLqDg3yDs8dtRj`. Association snapshot finalized slot 4778.
The old Pool `8YRunNHbLqBUzeZYh7VK6jsJDUup4jA1qTcKvPy4i2Lf` was not rewired or
migrated; no continuity of its notes or custody is claimed.

| Honest operation | CU | Local signature |
| --- | ---: | --- |
| transfer stage1 | 1207396 | `2x7VxbZU4iRvKxzboTtotrHjk5T4x2kW1wme8vLMsTdNEfpxXJFyZhpMx4KpeHDA6fDA6U1pMkBj21sjGUrMJc2U` |
| transfer stage2 | 1146054 | `2tePUHYXvNoKEbJo87QrxCs2bArysEGzRMAjzFyoavSzsBEHrT9VH8qNvxbxXfepSUAUpTMp656vSTiet7diRnpx` |
| withdrawal stage1 | 1206672 | `23ZavAfukN5Z89z2E1F8qtHfEQBoWpjrQmpY5xGt9aTTKQta69GdMvHsZN6aZkMkuWRfi146TYo7HWVoTHDypqqB` |
| withdrawal stage2 | 1152667 | `drL7QpEszNZEHmfuWud41sUE1ymmJJY2VoNLC2twTJuvS9pGJFzRRKddWWcW1yo98bTZgDfpGaNwPk3i4dRNBJw` |

Vault/destination balances were 2000/0 after transfer and 1750/250 after withdrawal.
Replays rejected NullifierAlreadyConsumed (0x41532026) without protected state changes.
Mutated proofs rejected InvalidInstructionData without changing fresh checkpoints;
original proof bytes were restored. `NDZ_final_spend/complete.json` records success.

All **1812 workflow transactions** have captured finalized metadata,
signature, CU and fee in NDZ_TRANSACTIONS.json / NDZ_METADATA.json.gz; total CU
13504306, fees 0.027440000 SOL. Initial payer balance minus
ending balance equals every live account's rent plus every fee exactly. Local peak
outlay was 11.997749120 SOL at the higher local rent rate;
ending payer 6.355454960 SOL. Final buffer inventory is empty.
The updated failure handler was exercised after buffer creation using a small
carrier-ELF buffer-only probe; it deployed no program, refunded the full buffer,
confirmed zero balance, captured both transaction metadata records and retained keys.
Its expected process exit is 1, not an on-chain error or memory failure.

## Resource / validation receipts

| Target | Exit | Wall seconds | Peak RSS KiB | Cgroup peak bytes | Swap peak bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| NDZ_final_deploy | 0 | 1023.68 | 44724 | 93925376 | 0 |
| NDZ_final_spend | 0 | 824.42 | 25168 | 25411584 | 0 |
| NDZ_final_failure | 1 | 34.25 | 32688 | 26972160 | 0 |

Validator: exit 0 after intentional SIGINT shutdown, wall 49:30.80, peak RSS
1419280 KiB, cgroup peak 3222011904 bytes, swap peak 0;
MemoryHigh=3G, MemoryMax=4G, no OOM/max events. Ledger and keys remain intact.
Every final runtime target records command, exact script hashes, core/client source revision and caps.
`#print axioms`: N/A for every target; no Lean target or formal manifest was replayed.
The optimized native client build and original proof-generation run have separate
GNU-time/cgroup receipts. Twelve policy tests and 31 existing lifecycle tests passed;
the complete runtime scenario supplies the final integration check.

## Reused evidence and limits

Reused NCY's exact frozen source-to-ELF reproduction, NDQ's historical dependency
association, and NDS's frozen-old-registry diagnosis. This worker independently
hashed the release and read-only downloaded loaded dependency ELFs; all hashes
match the pins. Stage 0 source/ELF inspection found no fixed verifier self-ID or
fixed verifier ID dependency in Pool/registry. No rebuild or patch was used.

The selected64 client generated one successful proof attempt for each fixture in
the first full local run (119.861601992 / 113.577715365 seconds). The final pass
reused those retained public proof artifacts through the validated resume path,
with identical local identities and deterministic normally initialized state.
NDZ_PROOF_REUSE.json and upload readback hashes identify them. This is not a second
independent proof sample or proving-time benchmark.

The first full run's CLI deployment/finalization metadata had pruned before collection;
it is diagnostic/proof-generation evidence, not the complete release receipt set.
The replacement added immediate CLI metadata capture and longer history retention.
The local RPC still ages some old signature-index entries; all 1812 final
records were captured immediately, every currently indexed transaction has a receipt,
and exact lamport conservation independently closes the accounting. There is no
missing metadata in the final set. NDZ_COLLECTION_AUDIT.json records this distinction.
The replay was justified by a specifically missing evidence artifact, not an unchanged
formal regression. Earlier ledgers, raw public receipts and all keys are retained.

Local runtime is pinned Agave 4.2.0 with cloned devnet features and older genesis
rent; devnet reports 4.4.0-beta.1 and lower rent. The local result does not establish
runtime equivalence. RPC/finality, pinned-build/source association and the existing
loader/registry/code premises remain trusted as before; no premise was discharged,
waived or reclassified by this task.

## Reviewed next deliverable, then stop

NDZ_DEVNET_RUNBOOK.md gives exact commands, expected outputs, funding, stop/rollback
points and rent ledger. Current read-only conservative public reserve is
**16.781526200 SOL**, headroom **1.571677880 SOL**;
permanently locked verifier rent **7.945450200 SOL**.
The no-close fixture budget is reported separately. No reused Pool/carrier program
is finalized. The Mac writer container was prepared, read-only checked, and generated a fresh
offline selected64 proof in 39.34 seconds, one attempt, with
cgroup memory peak 618475520 bytes and swap peak 0. Network was
disabled, no devnet key was mounted and no signature was generated.
NDZ_WRITER_PROVE_RESULT.json records this compatibility check. Eight fresh local
nonce-account keys and its private nonce store remain in the Mac evidence keys/
folder. The container uses the exact
rehearsed Linux client/CLI, a 4 GiB zero-swap cap and in-place retained key mounts.

Fresh devnet verifier key public identity:
`CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ`;
expected ProgramData `7GVKbnPt1XkYvnZURDLRKJqC89qbgfqP912hM3aUojRk`.
Key location/mode are in NDZ_KEY_RETENTION.md. No secret key bytes were printed,
copied, hashed or committed; all 31 host workflow key files, eight Mac offline-probe key files, plus validator internal
keys and their retained aliases remain present. No key cleanup occurred. Backup
status is not asserted because this worker was prohibited from copying secrets;
the lead must confirm the recovery policy's durable backup before public writing.

**L188 obligation 5 remains OPEN:** it needs the real devnet run and a read-only
association of its actual fresh Pool/registry/entry with the immutable release ELF.
Next deliverable is lead review, followed by a writer assigned by the lead under the existing owner approval executing
runbook steps 1–4 and delivering those real-devnet receipts/association. This worker
stops here; it does not execute the public write commands.
