#!/usr/bin/env python3
"""NPP_: extract the TX2 probe inputs (record 36, transfer-stage2, 10 November devnet): the verifier
CPI (program GqZzWuGT) issued by the Pool. Usage: python3 -I NPP_probe2_inputs.py <NPC_TRANSACTIONS.json.xz> <outdir>
Accounts are the CPI's 7 accounts in CPI order, with their TX2 pre-images. The recording does not
carry the caller's CPI privileges; they are taken from the Pool source that issues this CPI,
programs/aspis-pool/src/pair_forest_dispatch.rs:320-338 (both cfg variants): every CPI account is
AccountMeta::new_readonly(key, false), i.e. signer = 0, writable = 0. (v1 of this script used the
outer message flags; the model rejected with InvalidAccountData at require_verifier_checkpoint,
NPP_L034.) executable is the pre-image flag. Writes acc{i}.bin, post{i}.bin, accounts.txt, program.txt,
ixdata.txt, slot.txt, return.bin (the verifier's recorded return data) and NPP_PROBE2_INPUTS.json."""
import json, lzma, sys, os, base64, hashlib
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'host-ids-20261110'))
from NPO_base58 import b58decode
src, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
raw = open(src, 'rb').read(); d = json.loads(lzma.decompress(raw))
t = d['transactions'][36]
assert t['name'] == 'transfer-stage2' and t['meta']['err'] is None
m = t['transaction_json']['transaction']['message']; k = m['accountKeys']
cpis = [i for g in t['transaction_json']['meta']['innerInstructions'] for i in g['instructions']
        if k[i['programIdIndex']] == d['programs']['verifier']]
assert len(cpis) == 1
cpi = cpis[0]
alphabet = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
def b58(s):
    n = 0
    for c in s: n = n * 58 + alphabet.index(c)
    b = n.to_bytes((n.bit_length() + 7) // 8, 'big')
    pad = len(s) - len(s.lstrip('1'))
    return b'\0' * pad + b
ixdata = b58(cpi['data'])
flags = {f['key']: f for f in t['message_account_flags']}
pre = {a['key']: a for a in t['pre']['accounts']}; post = {a['key']: a for a in t['post']['accounts']}
lines, files = [], {}
for i, ai in enumerate(cpi['accounts']):
    key = k[ai]; a = pre[key]; f = flags[key]
    data = base64.b64decode(a['data_base64']) if a.get('data_base64') else b''
    pd = base64.b64decode(post[key]['data_base64']) if post[key].get('data_base64') else b''
    open(os.path.join(out, f'acc{i}.bin'), 'wb').write(data); open(os.path.join(out, f'post{i}.bin'), 'wb').write(pd)
    lines.append(f"{b58decode(key).hex()} {b58decode(a['owner']).hex()} 0 0 {int(a['executable'])}")
    files[f'acc{i}'] = {'key': key, 'owner': a['owner'], 'len': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
                        'post_len': len(pd), 'post_sha256': hashlib.sha256(pd).hexdigest(), 'changed_by_tx2': data != pd or a['lamports'] != post[key]['lamports'],
                        'message_is_signer': f['is_signer'], 'message_is_writable': f['is_writable'], 'cpi_is_signer': False, 'cpi_is_writable': False}
ret = [l for l in t['transaction_json']['meta']['logMessages'] if l.startswith('Program return: ' + d['programs']['verifier'])]
rb = base64.b64decode(ret[0].split()[-1]) if ret else b''
open(os.path.join(out, 'return.bin'), 'wb').write(rb)
open(os.path.join(out, 'accounts.txt'), 'w').write('\n'.join(lines) + '\n')
open(os.path.join(out, 'program.txt'), 'w').write(b58decode(d['programs']['verifier']).hex() + '\n')
open(os.path.join(out, 'ixdata.txt'), 'w').write(ixdata.hex() + '\n')
open(os.path.join(out, 'slot.txt'), 'w').write(str(t['tx_slot']) + '\n')
json.dump({'source': os.path.basename(src), 'source_sha256': hashlib.sha256(raw).hexdigest(), 'record': 36,
           'signature': t['signature'], 'slot': t['tx_slot'], 'cpi_ixdata_len': len(ixdata), 'cpi_ixdata_head': ixdata[:8].hex(),
           'cpi_privileges_source': 'programs/aspis-pool/src/pair_forest_dispatch.rs:320-338 (new_readonly, non-signer)', 'return_len': len(rb), 'return_sha256': hashlib.sha256(rb).hexdigest(), 'files': files},
          open(os.path.join(out, 'NPP_PROBE2_INPUTS.json'), 'w'), indent=1)
print(json.dumps(json.load(open(os.path.join(out, 'NPP_PROBE2_INPUTS.json'))), indent=1)[:2500])
