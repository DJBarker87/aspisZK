"""PIN2 W4: extract the PIN2 devnet fixture inputs from the run receipts and
cross-check them independently.  Run with python3 -I.  Writes inputs/ and
INPUTS.json beside this script; never writes to the receipts directory.

Cross-checks (each an assert):
  1. The stage1 pre/post images of proof and statement are identical (stage1
     does not write them) and the stage1 checkpoint was all-zero before.
  2. The 58,295-byte proof account = 688-byte upload header + a 57,607-byte
     proof that starts with the R1P3CB18 magic.  The verifier-written
     post-stage1 checkpoint binds sha256(proof) at [16,48), sha256(statement)
     at [48,80) and the c1 root proof[16:48] at [112,144); this is the
     on-chain confirmation of the header strip and of the statement bytes.
  3. The statement and proof account images equal the bytes reassembled from
     the upload-program transactions' instruction data (independent record).
  4. A Python re-implementation of r0::Public::public_bytes (section 9, read
     from the ASF8 statement by the Rust offsets) reproduces the release
     fixture's 1,455 recorded bytes and its seed exactly on the OLD statement;
     on the PIN2 statements it gives 1,520 (transfer) and 1,524 (withdrawal)
     bytes, the frame 75+n and the SHA-256 seed.
"""
import base64, hashlib, json, lzma, sys, subprocess
from pathlib import Path
HERE = Path(__file__).resolve().parent
RCPT = Path('/Users/dominic/aspis-lead-infra/pin2-run/receipts')
ZK = '/Users/dominic/ZK'
OUT = HERE / 'inputs'; OUT.mkdir(exist_ok=True)
sha = lambda b: hashlib.sha256(b).hexdigest()
P = 2147483647
HEADER = 688
DOMAIN = b'UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3'
PAY = 1880 - 216          # payment statement offset (pair_forest_terminal.rs)
LATE = 144                # late statement offset
SNAP = LATE + 32          # live snapshot inside the late statement

def words_ok(b):
    return all(int.from_bytes(b[i:i+4], 'little') < P for i in range(0, len(b), 4))

def public_bytes(st, pin2):
    """Section 9 of r0::Public::public_bytes, from ASF8 offsets."""
    assert len(st) == 1880 and st[:4] == b'ASF8'
    kind = st[5]
    pay = st[PAY:]
    assert pay[:4] in (b'ASCP', b'ASWP')
    transfer = pay[:4] == b'ASCP'
    assert kind == (1 if transfer else 2), (kind, pay[:4])   # PoolV1TransitionKind: PrivateTransfer = 1, Withdrawal = 2
    pool, domain = pay[8:40], pay[40:72]
    anchor, nullifier, asset = pay[80:112], pay[112:144], pay[144:148]
    out = bytearray([0 if transfer else 1])
    out += anchor + nullifier + asset
    if transfer:
        out += b'\x01' + pay[152:184]          # recipient commitment
        out += pay[184:216]                     # change commitment
        out += b'\x00'                          # no amount
    else:
        out += b'\x00'                          # no recipient
        out += pay[184:216]                     # change commitment
        out += b'\x01' + pay[148:152]           # amount
    out += st[SNAP+120:SNAP+128]                # live_snapshot.next_pair_index
    out += st[SNAP+160:SNAP+800]                # live_snapshot.frontier (20 x 32)
    out += st[992:1024]                         # candidate next_root
    out += st[1024:1664]                        # candidate next_frontier
    assert st[992-8:992] == (int.from_bytes(st[SNAP+120:SNAP+128], 'little') + 1).to_bytes(8, 'little')
    if pin2:
        out += pool + domain
        if transfer:
            out += b'\x00'
        else:
            out += b'\x01' + pay[152:184]       # destination token account
    words = bytes(out[1:65]) + bytes(out[65:69])
    assert words_ok(words)
    return bytes(out), transfer

def frame(pb, root):
    return DOMAIN + b'\x00' + len(pb).to_bytes(4, 'little') + pb + root

def main():
    res = {'receipts': str(RCPT), 'header_bytes_stripped': HEADER, 'spends': {}}
    # Old fixture: reproduce the release recorded bytes and seed.
    old_st = Path(ZK, 'docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/transfer-13/r1-s2-public-asf8.bin').read_bytes()
    old_pf = Path(ZK, 'docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/transfer-13/r1-s2-proof.bin').read_bytes()
    shain = json.loads(subprocess.run(['git', '-C', ZK, 'show', 'research:evidence/joint-fixture10-20261026/JFp_SHA_INPUT.json'], capture_output=True, text=True, check=True).stdout)
    old_msg = bytes(shain['message'])
    opb, _ = public_bytes(old_st, pin2=False)
    assert len(opb) == 1455 and frame(opb, old_pf[16:48]) == old_msg, 'old serializer model mismatch'
    assert list(hashlib.sha256(old_msg).digest()) == [228,169,34,97,252,244,53,226,26,140,30,138,162,243,99,242,206,9,102,152,190,134,67,110,159,218,112,61,208,157,117,30]
    res['old_fixture_check'] = {'statement_sha256': sha(old_st), 'proof_sha256': sha(old_pf),
        'public_bytes_len': len(opb), 'frame_len': len(old_msg), 'seed_sha256': sha(old_msg),
        'result': 'Python section-9 model reproduces JFp_SHA_INPUT.message and JFr_SeedBoundary.numeric'}
    for sp in ('transfer', 'withdrawal'):
        rec = json.loads((RCPT / 'PIN2_spend' / f'{sp}-stage1-recording.json').read_text())
        ins = rec['instructions'][0]
        assert ins['program'] == 'BLgzrkDiCs4f7bwWrP4EBSNN5nhi2snfoLopxs2X3xNg' and ins['data_hex'] == '030a'
        keys = dict(zip(['proof', 'statement', 'checkpoint'], [a['key'] for a in ins['accounts']]))
        img = {ph: {a['key']: a for a in rec[ph]['accounts']} for ph in ('pre', 'post')}
        get = lambda ph, role: base64.b64decode(img[ph][keys[role]]['data_base64'])
        acct, st = get('pre', 'proof'), get('pre', 'statement')
        assert acct == get('post', 'proof') and st == get('post', 'statement')
        assert get('pre', 'checkpoint') == bytes(1768)
        cp = get('post', 'checkpoint')
        pf = acct[HEADER:]
        assert len(acct) == 58295 and len(pf) == 57607 and pf[:8] == b'R1P3CB18'
        assert cp[:8] == b'R1P2CKP2' and len(cp) == 1768
        assert cp[16:48] == hashlib.sha256(pf).digest(), 'checkpoint does not bind sha256(proof)'
        assert cp[48:80] == hashlib.sha256(st).digest(), 'checkpoint does not bind sha256(statement)'
        assert cp[112:144] == pf[16:48]
        pb, transfer = public_bytes(st, pin2=True)
        fr = frame(pb, pf[16:48])
        # Independent record: reassemble the upload-program writes (data =
        # tag 0x01, seed length, seed, u32 LE offset, chunk) from the upload
        # transactions' instruction data and compare with the account images.
        def reassemble(kind, size, key):
            buf = bytearray(size); seen = bytearray(size); n = 0
            for f in sorted((RCPT / 'PIN2_spend').glob(f'{sp}-{kind}-upload-*-recording.json')):
                r = json.loads(f.read_text())
                for i2 in r['instructions']:
                    if i2['program'] != '9DYn3ykkW6JEgYVKst7y7Jd9SqxSjoSNUVTgnGCHWqx5' or i2['accounts'][0]['key'] != key:
                        continue
                    d = bytes.fromhex(i2['data_hex']); assert d[0] == 1
                    sl = d[1]; off = int.from_bytes(d[2+sl:6+sl], 'little'); chunk = d[6+sl:]
                    buf[off:off+len(chunk)] = chunk; seen[off:off+len(chunk)] = b'\x01' * len(chunk); n += 1
            return bytes(buf), all(seen), n
        st_tx, st_full, st_n = reassemble('statement', 1880, keys['statement'])
        pf_tx, pf_full, pf_n = reassemble('proof', 58295, keys['proof'])
        assert st_full and st_tx == st, 'statement upload transactions disagree with the account image'
        assert pf_full and pf_tx == acct, 'proof upload transactions disagree with the account image'
        tx_found = {'statement_upload_tx': st_n, 'proof_upload_tx': pf_n, 'equal_to_account_images': True}
        for name, b in (('proof', pf), ('statement', st), ('checkpoint', cp), ('public_bytes', pb), ('init_frame', fr)):
            (OUT / f'{sp}-{name}.bin').write_bytes(b)
        res['spends'][sp] = {
            'stage1_signature': rec['signature'], 'accounts': keys,
            'proof_account_bytes': len(acct), 'proof_account_sha256': sha(acct),
            'proof_bytes': len(pf), 'proof_sha256': sha(pf),
            'statement_bytes': len(st), 'statement_sha256': sha(st),
            'checkpoint_post_stage1_sha256': sha(cp),
            'checkpoint_binds_proof_and_statement_sha256': True,
            'public_bytes_len': len(pb), 'public_bytes_sha256': sha(pb),
            'pool_offset_in_public': len(pb) - (65 if transfer else 97),
            'init_frame_len': len(fr), 'seed_sha256': sha(fr),
            'upload_transactions_reassembled': tx_found,
        }
    res['expected'] = {'transfer_public': 1520, 'withdrawal_public': 1524}
    assert res['spends']['transfer']['public_bytes_len'] == 1520
    assert res['spends']['withdrawal']['public_bytes_len'] == 1524
    (HERE / 'INPUTS.json').write_text(json.dumps(res, indent=2) + '\n')
    print(json.dumps(res, indent=2))

if __name__ == '__main__':
    main()
