"""Render final human handoff from public measured receipts."""
import gzip,json,pathlib,re,subprocess
from decimal import Decimal
E=pathlib.Path(__file__).resolve().parent
def read(p):return json.loads((E/p).read_text())
def sol(n):return f'{Decimal(n)/Decimal(10**9):.9f}'
def resource(label):
 r=read(label+'-receipt.json');t=(E/(label+'.time')).read_text();rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',t).group(1)
 return f"| {label} | {r['exit']} | {r['wall_seconds']:.2f} | {rss} | {r['cgroup_memory_peak']} | {r['cgroup_swap_peak']} |"
S=read('NDZ_SUMMARY.json');F=read('NDZ_FUNDING.json');C=read('NDZ_local.json');K=read('NDZ_LOCAL_KEYS_PUBLIC.json');R=read('NDZ_RENT_LEDGER.json');P=read('NDZ_PROOF_REUSE.json')
assert S['transactions']==1812 and S['public_write_count']==0 and S['final_buffers']=={'buffers':[]} and F['funding_pass'] and F['signatures_generated']==0
assert not subprocess.check_output(['git','diff','4bb3b3f51e','HEAD','--','crates','programs'],cwd=E.parents[1])
complete=read('NDZ_final_spend/complete.json');assert complete['settled']==['transfer','withdrawal'] and len(complete['negative_checks'])==4
with gzip.open(E/'NDZ_METADATA.json.gz','rt') as f:meta=json.load(f)
rows=read('NDZ_TRANSACTIONS.json');assert len(meta)==len(rows)==1812 and {r['signature'] for r in rows}==set(meta)
assert sum(r['fee'] for r in rows)==S['fees_lamports'] and all(r['compute_units'] is not None for r in rows)
assert sum(r['err'] is not None for r in rows)==4
for label in ['transfer','withdrawal']:
 assert read('NDZ_final_spend/'+label+'-proof-upload-summary.json')['sha256']==P[label]['artifacts']['proof.bin']
 assert read('NDZ_final_spend/'+label+'-statement-upload-summary.json')['sha256']==P[label]['artifacts']['statement.bin']
with gzip.open(E/'NDZ_ASSOCIATION.json.gz','rt') as f:A=json.load(f)
assert A['fresh_pool'] and A['frozen_registry'] and A['active_release_entry'] and A['immutable_release_programdata']
W=read('NDZ_WRITER_PROVE_RESULT.json');assert W['exit']==0 and W['network']=='none' and W['signatures_generated']==0 and W['devnet_key_mounts']==0 and W['limits']['memory.swap.peak']=='0'
V=read('NDZ_VALIDATOR_RESOURCE.json');vtime=V['gnu_time'];vrss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',vtime).group(1);vwall=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)',vtime).group(1);vexit=re.search(r'Exit status: (\d+)',vtime).group(1)
spent=''
for label in ['transfer','withdrawal']:
 for stage in ['stage1','stage2']:
  q=read('NDZ_final_spend/'+label+'-'+stage+'.json');assert q['finalized'] and q['error'] is None
  spent+=f"| {label} {stage} | {q['compute_units']} | `{q['signature']}` |\n"
refund=read('NDZ_final_failure/verifier-failure-refund.json');assert refund['remaining_lamports']==0 and refund['key_retained']
refundrows=read('NDZ_final_failure/verifier-refund-signatures.json');refundsig=max(refundrows,key=lambda r:(r['slot'],r.get('transactionIndex',0)))['signature']
fixture=sum(x['devnet_rent_quote'] for x in R if 'data_bytes'in x and x['data_bytes'] not in (36,1563773));assert fixture==F['fixture_rent_lamports']
budget=f'''
## Measured rent and funding ledger

All numbers are SOL. Public amounts are finalized read-only rent quotes in
NDZ_FUNDING.json, not a public deployment measurement. Each created local account,
its actual lamports, current devnet quote and close/recovery classification is in
NDZ_RENT_LEDGER.json (28 fixture accounts, two verifier accounts, two closed buffers).

| Item | SOL | Meaning |
| --- | ---: | --- |
| Retained devnet payer | {sol(F['balance']['value'])} | Finalized read-only balance |
| Verifier ProgramData | {sol(F['rent_quotes']['1563773'])} | Permanently locked on finalization |
| Verifier Program stub | {sol(F['rent_quotes']['36'])} | Locked; no loader-v3 close path |
| Verifier total | {sol(F['verifier_permanently_locked_lamports'])} | Exact proposed permanent verifier rent |
| All fresh fixture accounts | {sol(F['fixture_rent_lamports'])} | Includes governance-controlled SPL accounts |
| Fixture rent budgeted as locked | {sol(F['fixture_locked_budget_lamports'])} | No demonstrated close path in unchanged programs |
| Combined locked budget | {sol(F['permanent_locked_budget_lamports'])} | Verifier plus no-close fixture budget |
| Potentially recoverable SPL rent | {sol(F['fixture_rent_lamports']-F['fixture_locked_budget_lamports'])} | Source can close now; destination requires token transfer first |
| Fee/retry reserve | {sol(F['fee_reserve_lamports'])} | Above measured normal-route fees |
| Conservative peak reserve | {sol(F['conservative_peak_lamports'])} | Buffer + Program/ProgramData + all fixtures + fee reserve |
| Headroom against payer | {sol(F['headroom_lamports'])} | Positive; funding check passes |
| Measured higher-rent local peak outlay | {sol(S['peak_payer_outlay_lamports'])} | Started with the same 18.353204080 SOL |
| Local workflow fees | {sol(S['fees_lamports'])} | Includes the deliberate buffer-failure probe |
| Local ending payer | {sol(S['final_balance']['value'])} | Fully reconciled against rent and fees |

The local validator uses the older 6,960-lamport rent rate; devnet currently uses
5,080. Local locked-budget lamports are {S['locked_lamports']}, and potentially
recoverable SPL rent is {S['recoverable_lamports']} lamports. No token-account cleanup
was executed. The source token balance is zero; the destination holds 250 tokens
in base units and must retain its authority until an approved transfer/close.
The small failure-test buffer returned 141294960 lamports to
`{refund['recipient']}`; close signature `{refundsig}` is local only. Both final
buffers are absent/zero. All keys remain retained.

The conservative public reserve intentionally counts both loader allocations;
the measured loader route reuses buffer funds before allocating ProgramData.
With unchanged fees, the normal public route is estimated at 0.027415 SOL in fees
(the local failure probe adds 0.000025 SOL). These are estimates; rerun step 1
immediately before the separately reviewed public write and stop if funding or
feature/dependency checks fail.
'''
p=E/'NDZ_DEVNET_RUNBOOK.md';text=p.read_text();text=text.split('\n## Measured rent and funding ledger')[0]+budget;p.write_text(text)
claim=f'''# NDZ handoff — local rehearsal PASS; public execution not performed

Established claim: the exact frozen release ELF can run at a fresh verifier address
under the unchanged deployed Pool and registry program IDs. The final local ledger
used the real-ID cloned Pool/registry/carrier programs, deployed the unmodified
1,563,728-byte release through the paced loader-v3 route, verified exact ProgramData
bytes and finalized it. Its fresh registry followed initialize → schedule → activate
→ freeze (generation 3, zero authority); the distinct fresh Pool then initialized.
Both honest transfer and withdrawal TX1/TX2 pairs and all four negative checks passed.
This is an operational identity/execution result, not a new soundness theorem.

Release SHA256: `{A['elf_sha256']}`.
Frozen core source: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.
All crates/programs remain identical to that revision. Only scripts/configuration,
policy tests and NDZ evidence changed. Script changes are committed separately.
No push, public transaction, public signed simulation, public airdrop or public
signature submission occurred. The retained devnet payer still had
{sol(F['balance']['value'])} SOL at finalized slot {F['balance']['context']['slot']}.

## Exact local result

RPC `{C['rpc_url']}`, genesis `{C['genesis_hash']}`.
Verifier `{C['programs']['verifier']}`, ProgramData `{A['addresses'][4]}`.
Fresh Pool `{A['addresses'][0]}`, registry `{A['addresses'][1]}`,
entry `{A['addresses'][2]}`. Association snapshot finalized slot {A['slot']}.
The old Pool `8YRunNHbLqBUzeZYh7VK6jsJDUup4jA1qTcKvPy4i2Lf` was not rewired or
migrated; no continuity of its notes or custody is claimed.

| Honest operation | CU | Local signature |
| --- | ---: | --- |
{spent}
Vault/destination balances were 2000/0 after transfer and 1750/250 after withdrawal.
Replays rejected NullifierAlreadyConsumed (0x41532026) without protected state changes.
Mutated proofs rejected InvalidInstructionData without changing fresh checkpoints;
original proof bytes were restored. `NDZ_final_spend/complete.json` records success.

All **{S['transactions']} workflow transactions** have captured finalized metadata,
signature, CU and fee in NDZ_TRANSACTIONS.json / NDZ_METADATA.json.gz; total CU
{S['compute_units']}, fees {sol(S['fees_lamports'])} SOL. Initial payer balance minus
ending balance equals every live account's rent plus every fee exactly. Local peak
outlay was {sol(S['peak_payer_outlay_lamports'])} SOL at the higher local rent rate;
ending payer {sol(S['final_balance']['value'])} SOL. Final buffer inventory is empty.
The updated failure handler was exercised after buffer creation using a small
carrier-ELF buffer-only probe; it deployed no program, refunded the full buffer,
confirmed zero balance, captured both transaction metadata records and retained keys.
Its expected process exit is 1, not an on-chain error or memory failure.

## Resource / validation receipts

| Target | Exit | Wall seconds | Peak RSS KiB | Cgroup peak bytes | Swap peak bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
{resource('NDZ_final_deploy')}
{resource('NDZ_final_spend')}
{resource('NDZ_final_failure')}

Validator: exit {vexit} after intentional SIGINT shutdown, wall {vwall}, peak RSS
{vrss} KiB, cgroup peak {V['cgroup_metrics']['memory.peak']} bytes, swap peak 0;
MemoryHigh=3G, MemoryMax=4G, no OOM/max events. Ledger and keys remain intact.
Every final runtime target records command, code hash, source revision and caps.
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
The local RPC still ages some old signature-index entries; all {S['transactions']} final
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
**{sol(F['conservative_peak_lamports'])} SOL**, headroom **{sol(F['headroom_lamports'])} SOL**;
permanently locked verifier rent **{sol(F['verifier_permanently_locked_lamports'])} SOL**.
The no-close fixture budget is reported separately. No reused Pool/carrier program
is finalized. The Mac writer container was prepared, read-only checked, and generated a fresh
offline selected64 proof in {W['wall_seconds']:.2f} seconds, one attempt, with
cgroup memory peak {W['limits']['memory.peak']} bytes and swap peak 0. Network was
disabled, no devnet key was mounted and no signature was generated.
NDZ_WRITER_PROVE_RESULT.json records this compatibility check. Eight fresh local
nonce-account keys and its private nonce store remain in the Mac evidence keys/
folder. The container uses the exact
rehearsed Linux client/CLI, a 4 GiB zero-swap cap and in-place retained key mounts.

Fresh devnet verifier key public identity:
`CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ`;
expected ProgramData `7GVKbnPt1XkYvnZURDLRKJqC89qbgfqP912hM3aUojRk`.
Key location/mode are in NDZ_KEY_RETENTION.md. No secret key bytes were printed,
copied, hashed or committed; all {len(K)} host workflow key files, eight Mac offline-probe key files, plus validator internal
keys and their retained aliases remain present. No key cleanup occurred. Backup
status is not asserted because this worker was prohibited from copying secrets;
the lead must confirm the recovery policy's durable backup before public writing.

**L188 obligation 5 remains OPEN:** it needs the real devnet run and a read-only
association of its actual fresh Pool/registry/entry with the immutable release ELF.
Next deliverable is lead review, followed by a writer assigned by the lead under the existing owner approval executing
runbook steps 1–4 and delivering those real-devnet receipts/association. This worker
stops here; it does not execute the public write commands.
'''
(E/'NDZ_HANDOFF.md').write_text(claim)
print({'handoff_written':True,'transactions':len(meta),'funding_pass':F['funding_pass'],'workflow_public_key_files':len(K)})
