#!/usr/bin/env python3
"""Check source/translation/differential receipts; makes no Lean closure claim."""
from pathlib import Path
import hashlib, io, json, subprocess, tarfile, tempfile

base = Path(__file__).resolve().parent
sha = lambda data: hashlib.sha256(data).hexdigest()

def bundle(path, digest, count):
    assert sha(path.read_bytes()) == digest, path
    with tarfile.open(path) as tf:
        result = {m.name: tf.extractfile(m).read() for m in tf if m.isfile()}
    assert len(result) == count
    for name, pin in json.loads(result['archive-members.json']).items():
        assert len(result[name]) == pin['bytes'] and sha(result[name]) == pin['sha256'], name
    assert not any(n.endswith('.key') for n in result)
    return result

files = bundle(base / 'decoder-translation-evidence.tar.gz',
    '67b995bd8ce6f3f70bf2a39594f9e0443bceae46d5fc4d7f6522bfb69e158f5d', 104)
reg = bundle(base.parent / 'terminal-decoder-regression-20261016/decoder-regression-evidence.tar.gz',
    '1fb74b011c08ace93d13b6b96639a6aaf1b309ac3ee18e159d0c56b6a788fc45', 71)

# Resolve all Git source pins in one blob batch; no proof or dependency replay.
manifests = [json.loads(files[v + '/input/source-pins.json']) for v in ['owned', 'literal', 'slice', 'range']]
requests = [(j['source_revision'], p, h) for j in manifests for p, h in j['kit_files'].items()]
requests += [(j['revision'], p, h) for j in [json.loads(reg[k + '-manifest.json']) for k in ['before', 'after']] for p, h in j['files'].items()]
trees = {}
for rev, _, _ in requests:
    if rev in trees:
        continue
    raw = subprocess.check_output(['git', 'ls-tree', '--full-tree', '-rz', rev], cwd=base)
    trees[rev] = {entry.split(b'\t', 1)[1].decode(): entry.split(b'\t', 1)[0].split()[2].decode()
                  for entry in raw.split(b'\0') if entry}
oids = sorted({trees[rev][p] for rev, p, _ in requests})
raw = subprocess.run(['git', 'cat-file', '--batch'], input=('\n'.join(oids) + '\n').encode(),
                     stdout=subprocess.PIPE, check=True, cwd=base).stdout
stream = io.BytesIO(raw); hashes = {}
for oid in oids:
    header = stream.readline().split(); assert header[0].decode() == oid and header[1] == b'blob'
    data = stream.read(int(header[2])); assert stream.read(1) == b'\n'; hashes[oid] = sha(data)
assert not stream.read()
for rev, path, digest in requests:
    assert hashes[trees[rev][path]] == digest, (rev, path)

receipts = []
for name, data in files.items():
    if name.endswith('/receipt.json'):
        r = json.loads(data)
        expected = 2 if name in ['owned/runs/aeneas-a/receipt.json', 'literal/runs/aeneas-a/receipt.json'] else 0
        assert r['exit_status'] == expected, name
        assert r['swaps'] == 0 and r['limits'] == {'memory.high': '6442450944', 'memory.max': '8589934592', 'memory.swap.max': '0'}
        receipts.append(name)
assert len(receipts) == 11
assert b'Could not match the contexts' in files['owned/runs/aeneas-a/stdout.log']
assert b'Payment' in files['literal/runs/aeneas-a/stdout.log']

# Re-run only the metadata adapter on retained LLBC; never the compiler.
with tempfile.TemporaryDirectory() as temp:
    root = Path(temp); adapter = root / 'adapter.py'; adapter.write_bytes(files['j1-rename-enum-constructors.py'])
    for variant in ['literal', 'slice', 'range']:
        original = root / (variant + '-input.llbc')
        output = root / (variant + '-output.llbc'); report = root / (variant + '-report.json')
        original.write_bytes(files[variant + '/extraction-a/TerminalDecoder.llbc'])
        subprocess.run(['python3', str(adapter), str(original), str(output), str(report)], check=True, stdout=subprocess.PIPE)
        assert output.read_bytes() == files[variant + '/extraction-a/TerminalDecoder-renamed.llbc']
        j = json.loads(report.read_text()); assert len(j['changes']) == 4 and j['restored_complete_json_equals_input']
trace = files['range/runs/trace-a/stdout.log']
assert sha(trace) == '628a3418096f93d769955ff18e7ac2f4e8fcb25b659b66aac3360204ad94efff'
assert len(trace) == 66622110 and trace.endswith(b'complete 20720\n')
assert json.loads(files['range/differential.json'])['byte_identical']
funs = files['range/extraction-a/generated-renamed/AspisR1TerminalDecoder/Funs.lean']
assert b'Slice.Insts.CoreCmpPartialEqArray.eq' not in funs

for name, data in reg.items():
    if name.endswith('/receipt.json'):
        r = json.loads(data); assert r['exit'] == 0 and r['swap_current_bytes'] == 0, name
        assert r['limits'] == {'memory.high': '8589934592', 'memory.max': '10737418240', 'memory.swap.max': '0'}
summary = json.loads(reg['SUMMARY.json']); comparison = summary['comparison']
assert comparison['delta'] == {'stage1': 172, 'stage2': -70, 'sum': 102}
for key in ['both_admitted_pairs_accepted', 'initial_images_equal', 'checkpoint_equal', 'asr8_equal']:
    assert comparison[key]
assert not comparison['setup_cu_included']
for kind, folder in [('baseline', 'before-sbf'), ('candidate', 'after-sbf-fresh-artifacts')]:
    assert sha(reg[folder + '/aspis_r1_cost_probe_program.so']) == summary[kind + '_elf_sha256']
assert b'1 passed; 0 failed' in reg['runs/after-counter/build.log']
print(f'PASS: 175 archive members, {len(requests)} Git source pins, 11 translation/native receipts, four regression receipts; exact 20,720-case trace; CU +102. Lean closure is not asserted.')
