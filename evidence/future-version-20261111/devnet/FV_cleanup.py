#!/usr/bin/env python3
"""Future-version one-transaction run: return the fixture token-account rent after a completed run.

usage: FV_cleanup.py FV_config.json RECEIPT_DIR

Runs only after complete.json exists. Burns the 250 base units the withdrawal paid to the fixture
destination account, then closes the fixture source and destination token accounts (owner = the
run's governance key), lamports to the payer. The mint, the Pool state, the registry entry and the
nullifier markers have no close path in the frozen programs and stay.
"""
import base64, json, pathlib, sys
import PIN2_lib as L
from PIN2_seed_accounts import b58decode as b58

C = L.init(sys.argv[1], sys.argv[2]); O = L.O
done = json.load(open(O / 'complete.json'))
ns = C['key_namespace']; govkey = str(pathlib.Path(C['key_dir']) / f'{ns}-spend-governance.json')
gov = json.load(open(O / 'mint-setup.json'))['token_owner']
mint, source, dest = done['mint'], done['source'], done['destination']
ix = lambda accounts, data: {'program': L.TOKEN, 'accounts': accounts, 'data': data.hex()}
before = {a: L.account(a)['value'] for a in (source, dest)}
amount = lambda v: int.from_bytes(base64.b64decode(v['data'][0])[64:72], 'little')
recovered = 0; rows = {}
for name, address in (('source', source), ('destination', dest)):
    v = before[address]
    if v is None:
        continue
    ixs = []
    if amount(v):
        ixs.append(ix([[address, False, True], [mint, False, True], [gov, True, False]], bytes([8]) + amount(v).to_bytes(8, 'little')))
    ixs.append(ix([[address, False, True], [C['payer'], False, True], [gov, True, False]], bytes([9])))
    r = L.send(f'cleanup-{name}-close', ixs, [L.PAYER_KEY, govkey])
    t = json.load(open(O / f'cleanup-{name}-close-transaction.json'))
    back = t['meta']['postBalances'][0] - t['meta']['preBalances'][0] + t['meta']['fee']
    assert back == v['lamports'] and L.account(address)['value'] is None, f'{name}: close did not return the rent'
    recovered += back; rows[name] = {'address': address, 'burned_base_units': amount(v), 'returned_lamports': back, 'fee': r['fee']}
L.write('cleanup', {'recovered_lamports': recovered, 'accounts': rows})
print(json.dumps({'recovered_lamports': recovered}))
