"""Independent Python cross-checks of the PIN2 native dump (hashlib only;
no Rust, no generator).  usage: python3 -I PIN2W5_crosscheck.py"""
import hashlib, json, sys
from pathlib import Path
H = Path(__file__).resolve().parent; I = H / 'inputs'
D = json.loads((H / 'PIN2W5_VALUES.json').read_text())
proof = (I / 'transfer-proof.bin').read_bytes(); stmt = (I / 'transfer-statement.bin').read_bytes()
pub = (I / 'transfer-public_bytes.bin').read_bytes(); ck = (I / 'transfer-checkpoint.bin').read_bytes()
P = 2147483647; out = []
def check(name, ok, **kw):
    out.append(dict(check=name, ok=bool(ok), **kw)); print('OK  ' if ok else 'FAIL', name, kw if not ok else ''); assert ok
le = lambda b: [int.from_bytes(b[i:i+4], 'little') for i in range(0, len(b), 4)]
sample = lambda b: [(int.from_bytes(b, 'little') // P**i) % P for i in range(4)]
# 1. transcript seed: SHA-256(DOMAIN, 0, le32 1520, public bytes (W4 Python model), c1 root = proof[16:48])
DOMAIN = b'UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3'   # r1_wire.rs (private-leaf-salts)
check('Rust semantic public_bytes equal W4 Python-model public bytes (1520)', D['results']['semantic_public_bytes'] == pub.hex() and len(pub) == 1520)
frame = DOMAIN + b'\x00' + (1520).to_bytes(4, 'little') + pub + proof[16:48]
check('initialisation frame is 1595 bytes and equals W4 inputs/transfer-init_frame.bin', len(frame) == 1595 and frame == (I / 'transfer-init_frame.bin').read_bytes())
seed = hashlib.sha256(frame).digest()
check('seed = sha256(frame) equals the native seed', seed.hex() == D['seed_hex'], seed=seed.hex())
check('seed equals W4 SHA-256 seed 17667969...50a1', seed.hex() == '17667969372a21c5833136bf944e8cc7fb0ab0e53ea40acfec66ca0afdd050a1')
# 2. first semantic sample (row 0): absorbed = H(seed,0,0xa0,frame0), read = H(absorbed,1), digits base P
r0 = D['semantic_rows'][0]; f0 = bytes(r0['frame'])
check('row-0 frame is the 5-byte empty header at proof[48:53]', f0 == proof[48:53] == bytes(5))
absorbed = hashlib.sha256(seed + bytes([0, 0xa0]) + f0).digest(); read = hashlib.sha256(absorbed + b'\x01').digest()
check('row-0 absorbed/read recomputed equal the native SHA calls', list(absorbed) == r0['absorbed'] and list(read) == r0['read'])
check('first semantic sample (lambda) = base-P digits of read = trace tag 0 index 0', sample(read) == D['tx1']['0']['0'][:4] and D['tx1']['0']['0'][4:] == [0, 0, 0, 0], value=sample(read))
# 3. whole semantic chain continuity: each row's before = previous after (H recomputed in Python)
st = seed; okc = True
for r in D['semantic_rows']:
    a = hashlib.sha256(st + bytes([0, 0xa0 + r['row']]) + bytes(r['frame'])).digest()
    okc &= (list(st) == r['before'] and list(a) == r['absorbed'] and list(hashlib.sha256(a + b'\x01').digest()) == r['read'])
    st = hashlib.sha256(a + b'\x02').digest(); okc &= list(st) == r['after']
check('27 semantic rows: Python SHA chain from the seed equals the native chain', okc and len(D['semantic_rows']) == 27)
check('samples 0..24 (15 challenges, 10 alphas) = base-P digits of the 25 reads', all(sample(bytes(D['semantic_rows'][i]['read'])) == D['tx1']['0'][str(i)][:4] for i in range(25)))
# 4. checkpoint fields
check('native stage-1 output equals the recorded checkpoint (1768 B)', D['results']['tx1_checkpoint'] == ck.hex() and D['results']['tx1_checkpoint_equals_recorded'] == 'true')
check('checkpoint [16,48) = sha256(proof)', ck[16:48] == hashlib.sha256(proof).digest())
check('checkpoint [48,80) = sha256(statement)', ck[48:80] == hashlib.sha256(stmt).digest())
check('checkpoint [112,144) = c1 root proof[16:48]', ck[112:144] == proof[16:48])
check('checkpoint trailer = sha256("UNPROVED:R1:checkpoint" || ck[:1736])', ck[1736:] == hashlib.sha256(b'UNPROVED:R1:checkpoint' + ck[:1736]).digest())
check('checkpoint semantic alphas [408,568) = base-P digits of reads 15..24', [le(ck[408+16*i:424+16*i]) for i in range(10)] == [sample(bytes(D['semantic_rows'][15+i]['read'])) for i in range(10)])
q = [int.from_bytes(ck[320+4*i:324+4*i], 'little') for i in range(22)]
check('checkpoint queries [320,408) = trace tag 5', q == [D['tx1']['5'][str(i)][0] for i in range(22)], queries=q)
check('checkpoint gamma [176,208) = trace tag 4 index 27', le(ck[176:208]) == D['tx1']['4']['27'])
op = D['opening_transcript']
check('opening transcript state0 = sha256(P3 domain, variant 2, semantic state after row 26)', bytes(op['state0']) == hashlib.sha256(b'UNPROVED:R1:PRIVATE-SALTED:P3' + b'\x02' + bytes(D['semantic_rows'][-1]['after'])).digest())
check('checkpoint state [80,112) = final opening transcript state (after rho)', list(ck[80:112]) == op['final_state'])
check('stage 2 accepted (authenticated and strict)', D['results']['tx2_result'] == 'Ok(())' and D['results']['tx2_strict_result'] == 'Ok(())')
# 5. inputs against the raw devnet recording (not via W4's files)
import base64
rec = json.loads(Path('/Users/dominic/aspis-lead-infra/pin2-run/receipts/PIN2_spend/transfer-stage1-recording.json').read_text())
acc = {a['key']: base64.b64decode(a['data_base64']) for a in rec['post']['accounts']}
keys = [a['key'] if isinstance(a, dict) else a for a in rec['instructions'][0]['accounts']]
pa, sa, ca = (acc[k] for k in keys)
check('recording: stage-1 instruction data is [3,10] and meta.err is null', rec['instructions'][0]['data_hex'] == '030a' and rec['meta'].get('err') is None)
check('recording: proof account data[688:] = proof (57,607 B)', pa[688:] == proof and len(pa) == 688 + 57607)
check('recording: statement account = statement', sa == stmt)
check('recording: post-stage-1 checkpoint account = checkpoint', ca == ck)
(H / 'CROSSCHECK.json').write_text(json.dumps(out, indent=1) + '\n'); print(len(out), 'checks passed')
