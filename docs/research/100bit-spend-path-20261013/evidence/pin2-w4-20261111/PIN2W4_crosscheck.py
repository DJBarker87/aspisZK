"""Independent read-back: parse the regenerated Lean sources (not the
generators) and compare every literal byte window with the raw recording.
  - RPz8_JFx_Data*: concatenated chunk literals == proof / statement /
    checkpoint taken from the stage1 recording (sha256 compared).
  - NDO_JFz_ScanNN: data literal == proof[off:off+n] for the stated offset.
  - NDO_JFu_PublicDigestNN / PublicMetaNN / NDO_JFs_CellNN: literal ==
    statement[off:off+n] and the stated length n.
  - NDO_JFp_SHABlockNN: inputs concatenate to SHA-256 padding of the PIN2
    initialisation frame, whose public-bytes slice [43, 43+1520) is the
    Python section-9 serialization and whose length field is 1520.
"""
import base64, hashlib, json, re
from pathlib import Path
HERE = Path(__file__).resolve().parent; SRC = HERE / 'sources'
RC = Path('/Users/dominic/aspis-lead-infra/pin2-run/receipts/PIN2_spend/transfer-stage1-recording.json')
rec = json.loads(RC.read_text()); keys = [a['key'] for a in rec['instructions'][0]['accounts']]
img = {a['key']: base64.b64decode(a['data_base64']) for a in rec['post']['accounts']}
proof, stmt, cp = img[keys[0]][688:], img[keys[1]], img[keys[2]]
def lit(s):
    out = []
    for m in re.finditer(r'List\.replicate (\d+) (\d+)#u8|\[((?:\d+#u8,?)+)\]', s):
        if m.group(1): out += [int(m.group(2))] * int(m.group(1))
        else: out += [int(x) for x in re.findall(r'(\d+)#u8', m.group(3))]
    return bytes(out)
def chunks(t):
    return b''.join(lit(l.split(':=', 1)[1]) for l in t.splitlines() if re.match(r'def c\d+ : List U8 :=', l))
res = {}
pf = b''.join(chunks((SRC / f'RPz8_JFx_DataProof{i:02}.lean').read_text()) if (SRC / f'RPz8_JFx_DataProof{i:02}.lean').exists() else None for i in range(14))
# DataProof14 is text-identical to the release; read it from research
import subprocess
pf += chunks(subprocess.run(['git', '-C', '/Users/dominic/ZK', 'show', 'research:evidence/replay-dry9-20261027/RPz8_JFx_DataProof14.lean'], capture_output=True, text=True, check=True).stdout)
assert pf == proof, 'proof data modules disagree with the recording'
assert chunks((SRC / 'RPz8_JFx_DataPublic00.lean').read_text()) == stmt
assert chunks((SRC / 'RPz8_JFx_DataCheckpoint00.lean').read_text()) == cp
res['data'] = {'proof_sha256': hashlib.sha256(pf).hexdigest(), 'statement_sha256': hashlib.sha256(stmt).hexdigest(), 'checkpoint_sha256': hashlib.sha256(cp).hexdigest()}
n = 0
for f in sorted(SRC.glob('NDO_JFz_Scan*.lean')):
    t = f.read_text(); off = int(re.search(r'theorem selected : \(JFx_NativeBytes\.proof\.val\.drop (\d+)\)\.take (\d+) = data', t).group(1))
    ln = int(re.search(r'theorem length : data\.length = (\d+)', t).group(1))
    leaves = b''.join(lit(m.group(1)) for m in re.finditer(r'def b\d+ : List U8 := (\[.*?\])', t))
    assert leaves == proof[off:off+ln] and len(leaves) == ln, f; n += 1
res['scan_modules_checked'] = n
n = 0; lens = {}
for f in sorted(list(SRC.glob('NDO_JFu_PublicDigest*.lean')) + list(SRC.glob('NDO_JFu_PublicMeta*.lean')) + list(SRC.glob('NDO_JFs_Cell*.lean'))):
    t = f.read_text(); m = re.search(r'publicInput\.val\.drop (\d+)\)\.take (\d+)', t) or re.search(r'DataPublic00\.bytes\.drop (\d+)\)\.take (\d+)', t)
    off, ln = int(m.group(1)), int(m.group(2))
    b = lit(re.search(r'def bytes : List U8 := (\[.*?\])', t).group(1))
    assert b == stmt[off:off+ln] and len(b) == ln, f; n += 1; lens[f.stem] = [off, ln]
res['statement_window_modules_checked'] = n; res['statement_windows'] = lens
blocks = [bytes(int(x) for x in re.search(r'def input : List Nat := \[(.*?)\]', (SRC / f'NDO_JFp_SHABlock{i:02}.lean').read_text()).group(1).split(',')) for i in range(26)]
padded = b''.join(blocks); frame = (HERE / 'inputs/transfer-init_frame.bin').read_bytes()
assert padded == frame + b'\x80' + bytes(1664 - len(frame) - 9) + (8 * len(frame)).to_bytes(8, 'big')
assert int.from_bytes(frame[39:43], 'little') == 1520 and frame[43:43+1520] == (HERE / 'inputs/transfer-public_bytes.bin').read_bytes()
res['sha_blocks'] = {'blocks': 26, 'frame_len': len(frame), 'public_len_field': 1520, 'pool_slice': [43+1455, 32], 'domain_slice': [43+1487, 32], 'has_destination_byte_at': 43+1519}
assert frame[43+1455:43+1487] == stmt[1672:1704] and frame[43+1487:43+1519] == stmt[1704:1736] and frame[43+1519] == 0
(HERE / 'CROSSCHECK.json').write_text(json.dumps(res, indent=2) + '\n'); print(json.dumps({k: v for k, v in res.items() if k != 'statement_windows'}, indent=2))
