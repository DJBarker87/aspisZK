#!/usr/bin/env python3
"""PIN2 devnet collector (NPC_collect_devnet.py adapted). Read-only: receipts plus finalized RPC; never opens keys.

usage: PIN2_collect_devnet.py PIN2_devnet.json RECEIPT_ROOT
  RECEIPT_ROOT/PIN2_spend.log    driver stdout (one line per landed transaction)
  RECEIPT_ROOT/PIN2_spend/       the driver's receipt directory

Outputs in RECEIPT_ROOT:
  PIN2_TRANSACTIONS.json.xz  every recorded transaction (signed bytes, instruction metas/data,
                             pre/post account images, flags, Clock slot/blockTime, logs, CU, fee, err)
  PIN2_SUMMARY.json          one row per transaction, totals, per-payment close accounting and
                             the payer conservation check
  PIN2_REPLAY/<name>-ixN.json  program-run inputs for every Pool/verifier/registry/upload instruction
  PIN2_ASSOCIATION.json      finalized snapshot: Pool master, registry, entry, vault, program data

Conservation (payer): payer_start - payer_end == total fees + rent of every account the run
created that is still live (the rent ledger: fixtures, registry, Pool state, pages, nullifier
markers). Per payment: the close transactions recovered exactly the rent of the closed accounts,
and the payment's payer delta equals its fees plus the nullifier marker (plus a page if created).
"""
import base64, hashlib, json, lzma, pathlib, sys
from r1_devnet_rpc import rpc
from PIN2_seed_accounts import b58encode

C = json.load(open(sys.argv[1])); E = pathlib.Path(sys.argv[2]); R = E / 'PIN2_spend'; URL = C['rpc_url']
P = C['programs']; UP = C['upload_program']
ROLE = {P['pool']: 'pool', P['verifier']: 'verifier', P['registry']: 'registry', UP: 'upload',
        '11111111111111111111111111111111': 'system', 'TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA': 'spl-token'}
order = [l.split(' ', 1)[0] for l in (E / 'PIN2_spend.log').read_text().splitlines() if l and not l.startswith(' ') and ' {' in l]
recs = []
for name in order:
    f = R / f'{name}-recording.json'
    if not f.exists():
        raise SystemExit(f'missing recording for {name}')
    recs.append(json.loads(f.read_text()))
missing = sorted({p.name[:-len('-transaction.json')] for p in R.glob('*-transaction.json')} - set(order))
assert not missing, missing
A = {k: pathlib.Path(v['path']) for k, v in C['release_artifacts'].items()}
elf = {P['pool']: A['pool'], P['verifier']: A['devnet_verifier'], P['registry']: A['registry'], UP: A['upload']}
rows, replay_dir = [], E / 'PIN2_REPLAY'; replay_dir.mkdir(exist_ok=True)
for r in recs:
    pre = {a['key']: a for a in r['pre']['accounts']}; post = {a['key']: a for a in r['post']['accounts']}
    ix0 = r['instructions'][0]; d0 = bytes.fromhex(ix0['data_hex'])
    rows.append({'name': r['name'], 'signature': r['signature'], 'slot': r['tx_slot'], 'block_time': r['clock']['unix_timestamp_from_blockTime'],
                 'programs': [ROLE.get(i['program'], i['program']) for i in r['instructions']],
                 'magic': d0[:4].decode('latin1') if len(d0) >= 4 and all(32 <= b < 127 for b in d0[:4]) else d0[:4].hex(),
                 'data_bytes': len(d0), 'data_sha256': hashlib.sha256(d0).hexdigest(),
                 'compute_units': r['meta'].get('computeUnitsConsumed'), 'fee': r['meta']['fee'], 'err': r['meta']['err'],
                 'negative': r['negative'], 'accounts': len(r['keys']), 'accounts_changed': sorted(k for k in pre if pre[k] != post[k]),
                 'payer_delta': post[C['payer']]['lamports'] - pre[C['payer']]['lamports'],
                 'inner_instruction_count': sum(len(x['instructions']) for x in r['meta'].get('innerInstructions') or []),
                 'log_lines': len(r['meta'].get('logMessages') or []), 'isolated': r['isolation']['isolated'], 'serialized_bytes': r['serialized_bytes']})
    for n, ix in enumerate(r['instructions']):
        if ix['program'] in elf:
            accts = [{'key': a['key'], 'owner': pre[a['key']].get('owner', '11111111111111111111111111111111'), 'is_signer': a['is_signer'],
                      'is_writable': a['is_writable'], 'lamports': pre[a['key']].get('lamports', 0),
                      'data': list(base64.b64decode(pre[a['key']]['data_base64'])) if pre[a['key']].get('exists') else []} for a in ix['accounts']]
            (replay_dir / f"{r['name']}-ix{n}.json").write_text(json.dumps({'program_id': ix['program'], 'elf': str(elf[ix['program']]), 'accounts': accts,
                                                                           'instruction_data': list(bytes.fromhex(ix['data_hex']))}))
blob = json.dumps({'kind': 'PIN2_DEVNET_TRANSACTIONS', 'rpc': URL, 'genesis': C['genesis_hash'], 'programs': P, 'upload_program': UP,
                   'count': len(recs), 'transactions': recs}).encode()
(E / 'PIN2_TRANSACTIONS.json.xz').write_bytes(lzma.compress(blob, preset=9))
payer0 = {a['key']: a for a in recs[0]['pre']['accounts']}[C['payer']]['lamports']
payer1 = rpc(URL, 'getBalance', [C['payer'], {'commitment': 'finalized'}])['value']
fees = sum(r['fee'] for r in rows); payer_delta = sum(r['payer_delta'] for r in rows)
ledger = json.loads((R / 'rent-ledger.json').read_text()); left = sum(x['lamports'] for x in ledger)
complete = json.loads((R / 'complete.json').read_text())
payments = complete['payments']
assoc = {}
setup = json.loads((R / 'setup-plan.json').read_text())
for k in ['master', 'registry_account', 'entry', 'vault']:
    v = rpc(URL, 'getAccountInfo', [setup[k], {'encoding': 'base64', 'commitment': 'finalized'}])
    assoc[k] = {'address': setup[k], 'slot': v['context']['slot'], 'owner': v['value']['owner'], 'lamports': v['value']['lamports'],
                'data_sha256': hashlib.sha256(base64.b64decode(v['value']['data'][0])).hexdigest(), 'data_base64': v['value']['data'][0]}
for role, program in [('verifier', P['verifier']), ('pool', P['pool']), ('upload', UP)]:
    prog = rpc(URL, 'getAccountInfo', [program, {'encoding': 'base64', 'commitment': 'finalized'}])['value']
    assert prog['owner'] == 'BPFLoaderUpgradeab1e11111111111111111111111' and prog['executable']
    pd = b58encode(base64.b64decode(prog['data'][0])[4:36])
    v = rpc(URL, 'getAccountInfo', [pd, {'encoding': 'base64', 'commitment': 'finalized'}]); d = base64.b64decode(v['value']['data'][0])
    assoc[role + '_programdata'] = {'address': pd, 'slot': v['context']['slot'], 'authority_option': d[12],
                                    'authority': (b58encode(d[13:45]) if d[12] == 1 else None), 'program': program,
                                    'payload_sha256_at_artifact_length': hashlib.sha256(d[45:45 + C['release_artifacts'][{'verifier': 'devnet_verifier', 'pool': 'pool', 'upload': 'upload'}[role]]['bytes']]).hexdigest()}
(E / 'PIN2_ASSOCIATION.json').write_text(json.dumps({'setup_plan_keys': sorted(setup), 'snapshot': assoc}, indent=1) + '\n')
summary = {'transactions': len(rows), 'all_isolated': all(r['isolated'] for r in rows), 'total_cu': sum(r['compute_units'] or 0 for r in rows),
           'total_fees_lamports': fees, 'payer_start_lamports': payer0, 'payer_end_lamports': payer1,
           'payer_delta_from_recordings': payer_delta, 'payer_delta_matches_balance': payer0 + payer_delta == payer1,
           'rent_left_live_lamports': left, 'rent_ledger_rows': len(ledger),
           'conservation_payer_spend_eq_fees_plus_live_rent': payer0 - payer1 == fees + left,
           'payments': payments,
           'recovered_per_payment_lamports': {k: v['recovered_lamports'] for k, v in payments.items()},
           'close_rows': [r for r in rows if r['name'].endswith('-close')],
           'replay_inputs': sorted(p.name for p in replay_dir.glob('*.json')),
           'transactions_xz_sha256': hashlib.sha256((E / 'PIN2_TRANSACTIONS.json.xz').read_bytes()).hexdigest(),
           'transactions_json_sha256': hashlib.sha256(blob).hexdigest(), 'rows': rows}
(E / 'PIN2_SUMMARY.json').write_text(json.dumps(summary, indent=1) + '\n')
print(json.dumps({k: v for k, v in summary.items() if k not in ('rows', 'replay_inputs', 'payments', 'close_rows')}, indent=1))
for r in rows:
    if r['programs'][0] in ('pool', 'verifier', 'upload') and not r['name'].split('-')[-1].isdigit() or r['negative']:
        print(r['name'], r['magic'], r['compute_units'], r['fee'], r['err'], r['signature'])
assert summary['payer_delta_matches_balance'] and summary['conservation_payer_spend_eq_fees_plus_live_rent'], 'payer conservation failed'
