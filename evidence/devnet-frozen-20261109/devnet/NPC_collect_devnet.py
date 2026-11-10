"""NPC_ B1 devnet collector (NPC_collect_local.py adapted: paths, payer start from the first pre-image, association from config). Read-only: reads receipts and loopback RPC; never opens key files.

Outputs (in out/):
  NPC_LOCAL_TRANSACTIONS.json.xz  every recorded transaction: signed wire bytes, instruction metas and data,
                                  pre/post account images, message flags, Clock slot/blockTime, logs, inner
                                  instructions, CU, fee, err, isolation check, jsonParsed transaction.
  NPC_LOCAL_SUMMARY.json          one row per transaction plus totals and conservation check.
  NPC_REPLAY/<name>.json          agave-ledger-tool `program run` inputs for every Pool/verifier/registry
                                  instruction, built from the exact pre-state images.
  NPC_LOCAL_ASSOCIATION.json      one finalized snapshot: Pool master, registry, entry, verifier/Pool ProgramData.
"""
import base64, hashlib, json, lzma, pathlib, sys
AL='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
def base58e(b):
    n = int.from_bytes(b, 'big'); s = ''
    while n: n, r = divmod(n, 58); s = AL[r] + s
    return '1' * (len(b) - len(b.lstrip(b'\0'))) + s
E = pathlib.Path('/Users/dominic/ZK/.worktrees/cx-devnet2/evidence/devnet-frozen-20261109'); A = E / 'devnet/artifacts'
from r1_devnet_rpc import rpc
O = E / 'devnet/NPC_devnet_receipts'; R = O / 'NPC_spend'; C = json.load(open(E / 'devnet/NPC_devnet.json')); URL = C['rpc_url']
P = C['programs']; ROLE = {P['pool']: 'pool', P['verifier']: 'verifier', P['registry']: 'registry', C['carrier']: 'carrier',
                          '11111111111111111111111111111111': 'system', 'TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA': 'spl-token'}
order = [l.split(' ', 1)[0] for l in (O / 'NPC_spend.log').read_text().splitlines() if l and not l.startswith(' ') and ' {' in l]
recs = []
for name in order:
    f = R / f'{name}-recording.json'
    if not f.exists():
        raise SystemExit(f'missing recording for {name}')
    recs.append(json.loads(f.read_text()))
missing = sorted({p.name[:-len('-transaction.json')] for p in R.glob('*-transaction.json')} - set(order))
assert not missing, missing
rows, replay_dir = [], O / 'NPC_REPLAY'; replay_dir.mkdir(exist_ok=True)
elf = {P['pool']: str(A / 'pool.so'), P['verifier']: str(A / 'verifier-retarget.so'), P['registry']: str(A / 'registry.so')}
for r in recs:
    pre = {a['key']: a for a in r['pre']['accounts']}; post = {a['key']: a for a in r['post']['accounts']}
    changed = sorted(k for k in pre if pre[k] != post[k])
    ix0 = r['instructions'][0]
    rows.append({'name': r['name'], 'signature': r['signature'], 'slot': r['tx_slot'], 'block_time': r['clock']['unix_timestamp_from_blockTime'],
                 'programs': [ROLE.get(i['program'], i['program']) for i in r['instructions']],
                 'magic': bytes.fromhex(ix0['data_hex'][:8]).decode('latin1') if all(32 <= b < 127 for b in bytes.fromhex(ix0['data_hex'][:8])) else ix0['data_hex'][:8],
                 'data_bytes': len(ix0['data_hex']) // 2, 'data_sha256': hashlib.sha256(bytes.fromhex(ix0['data_hex'])).hexdigest(),
                 'compute_units': r['meta'].get('computeUnitsConsumed'), 'fee': r['meta']['fee'], 'err': r['meta']['err'],
                 'negative': r['negative'], 'accounts': len(r['keys']), 'accounts_changed': changed,
                 'inner_instruction_count': sum(len(x['instructions']) for x in r['meta'].get('innerInstructions') or []),
                 'log_lines': len(r['meta'].get('logMessages') or []), 'isolated': r['isolation']['isolated'],
                 'serialized_bytes': r['serialized_bytes']})
    for n, ix in enumerate(r['instructions']):
        if ix['program'] in elf:
            accts = []
            for a in ix['accounts']:
                s = pre[a['key']]
                accts.append({'key': a['key'], 'owner': s.get('owner', '11111111111111111111111111111111'), 'is_signer': a['is_signer'],
                              'is_writable': a['is_writable'], 'lamports': s.get('lamports', 0),
                              'data': list(base64.b64decode(s['data_base64'])) if s.get('exists') else []})
            (replay_dir / f"{r['name']}-ix{n}.json").write_text(json.dumps({'program_id': ix['program'], 'accounts': accts,
                                                                           'instruction_data': list(bytes.fromhex(ix['data_hex']))}))
blob = json.dumps({'kind': 'NPC_DEVNET_TRANSACTIONS', 'rpc': URL, 'genesis': C['genesis_hash'], 'programs': P, 'carrier': C['carrier'],
                   'count': len(recs), 'transactions': recs}).encode()
(O / 'NPC_TRANSACTIONS.json.xz').write_bytes(lzma.compress(blob, preset=9))
payer0 = {a['key']: a for a in recs[0]['pre']['accounts']}[C['payer']]['lamports']; payer1 = rpc(URL, 'getBalance', [C['payer'], {'commitment': 'finalized'}])['value']
fees = sum(r['fee'] for r in rows)
ledger = json.loads((R / 'rent-ledger.json').read_text()); rent = sum(x['lamports'] for x in ledger)
# Payer-funded rent includes accounts later drained/closed; conservation uses every payer delta in the recordings.
payer_delta = 0
for r in recs:
    pre = {a['key']: a for a in r['pre']['accounts']}; post = {a['key']: a for a in r['post']['accounts']}
    payer_delta += post[C['payer']]['lamports'] - pre[C['payer']]['lamports']
assoc = {}
setup = json.loads((R / 'setup-plan.json').read_text())
for k in ['master', 'registry_account', 'entry', 'vault']:
    if k in setup:
        v = rpc(URL, 'getAccountInfo', [setup[k], {'encoding': 'base64', 'commitment': 'finalized'}])
        assoc[k] = {'address': setup[k], 'slot': v['context']['slot'], 'owner': v['value']['owner'], 'lamports': v['value']['lamports'],
                    'data_sha256': hashlib.sha256(base64.b64decode(v['value']['data'][0])).hexdigest(), 'data_base64': v['value']['data'][0]}
PD = {'verifier': '9f4huzXEK5opApGDh1jvVVPPjnNdQJnCMUr3YcBbePsF', 'pool': '8aCcqmxpGhq5un6hcxQBFRGYhpAC5oCpAUwDUneR2jyL'}
for role in ['verifier', 'pool']:
    prog = rpc(URL, 'getAccountInfo', [P[role], {'encoding': 'base64', 'commitment': 'finalized'}])['value']
    assert prog['owner'] == 'BPFLoaderUpgradeab1e11111111111111111111111' and prog['executable']
    from r1_devnet_release_gate import base58; assert base64.b64decode(prog['data'][0])[4:36] == base58(PD[role])
    p = {'programdata': PD[role]}; v = rpc(URL, 'getAccountInfo', [p['programdata'], {'encoding': 'base64', 'commitment': 'finalized'}])
    d = base64.b64decode(v['value']['data'][0])
    assoc[role + '_programdata'] = {'address': p['programdata'], 'slot': v['context']['slot'], 'authority_option': d[12],
                                    'authority': (base58e(d[13:45]) if d[12] == 1 else None), 'program': P[role],
                                    'payload_sha256': hashlib.sha256(d[45:]).hexdigest(), 'payload_bytes': len(d) - 45}
(O / 'NPC_ASSOCIATION.json').write_text(json.dumps({'setup_plan_keys': sorted(setup), 'snapshot': assoc}, indent=1) + '\n')
summary = {'transactions': len(rows), 'all_isolated': all(r['isolated'] for r in rows), 'total_cu': sum(r['compute_units'] or 0 for r in rows),
           'total_fees_lamports': fees, 'payer_start_lamports': payer0, 'payer_end_lamports': payer1,
           'payer_delta_from_recordings': payer_delta, 'payer_delta_matches_balance': payer0 + payer_delta == payer1,
           'rent_ledger_lamports': rent, 'rent_ledger_rows': len(ledger), 'replay_inputs': sorted(p.name for p in replay_dir.glob('*.json')),
           'transactions_xz_sha256': hashlib.sha256((O / 'NPC_TRANSACTIONS.json.xz').read_bytes()).hexdigest(),
           'transactions_json_sha256': hashlib.sha256(blob).hexdigest(), 'rows': rows}
(O / 'NPC_SUMMARY.json').write_text(json.dumps(summary, indent=1) + '\n')
print(json.dumps({k: v for k, v in summary.items() if k not in ('rows', 'replay_inputs')}, indent=1))
for r in rows:
    if r['programs'][0] in ('pool', 'verifier') or r['negative']:
        print(r['name'], r['magic'], r['compute_units'], r['err'], r['signature'])
