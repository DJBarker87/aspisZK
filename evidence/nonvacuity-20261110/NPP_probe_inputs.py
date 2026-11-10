#!/usr/bin/env python3
"""NPP_: extract the timing-probe inputs for record 35 (transfer-stage1, 10 November devnet).
Usage: python3 -I NPP_probe_inputs.py <NPC_TRANSACTIONS.json.xz> <outdir>
Writes acc0.bin acc1.bin acc2.bin (pre-image data of the three instruction accounts, in
instruction order), ckpt_post.bin (post-image of account 2), accounts.txt (one line per account:
key-hex owner-hex is_signer is_writable executable), program.txt, ixdata.txt, and
NPP_PROBE_INPUTS.json (source sha256 and per-file sha256)."""
import json, lzma, sys, os, base64, hashlib
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'host-ids-20261110'))
from NPO_base58 import b58decode
src, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
raw = open(src, 'rb').read()
d = json.loads(lzma.decompress(raw))
t = d['transactions'][35]
assert t['name'] == 'transfer-stage1' and t['meta']['err'] is None
ix = t['instructions'][0]
assert ix['program'] == d['programs']['verifier']
pre = {a['key']: a for a in t['pre']['accounts']}
post = {a['key']: a for a in t['post']['accounts']}
lines = []
files = {}
for i, m in enumerate(ix['accounts']):
    a = pre[m['key']]
    data = base64.b64decode(a['data_base64'])
    open(os.path.join(out, f'acc{i}.bin'), 'wb').write(data)
    lines.append(f"{b58decode(m['key']).hex()} {b58decode(a['owner']).hex()} {int(m['is_signer'])} {int(m['is_writable'])} {int(a['executable'])}")
    files[f'acc{i}.bin'] = {'key': m['key'], 'owner': a['owner'], 'len': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
ck = base64.b64decode(post[ix['accounts'][2]['key']]['data_base64'])
open(os.path.join(out, 'ckpt_post.bin'), 'wb').write(ck)
files['ckpt_post.bin'] = {'len': len(ck), 'sha256': hashlib.sha256(ck).hexdigest()}
open(os.path.join(out, 'accounts.txt'), 'w').write('\n'.join(lines) + '\n')
open(os.path.join(out, 'program.txt'), 'w').write(b58decode(ix['program']).hex() + '\n')
open(os.path.join(out, 'ixdata.txt'), 'w').write(ix['data_hex'] + '\n')
json.dump({'source': os.path.basename(src), 'source_sha256': hashlib.sha256(raw).hexdigest(), 'record': 35,
           'signature': t['signature'], 'slot': t['tx_slot'], 'program': ix['program'], 'ixdata': ix['data_hex'],
           'cu': t['meta']['computeUnitsConsumed'], 'files': files}, open(os.path.join(out, 'NPP_PROBE_INPUTS.json'), 'w'), indent=1)
print(json.dumps(files, indent=1))
