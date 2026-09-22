#!/usr/bin/env python3
"""Fast integrity audit, not a repeated Rust/SBF/security regression."""
import argparse, ast, hashlib, json, subprocess, sys, tempfile
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--output', type=Path)
a = p.parse_args()
root = Path(__file__).resolve().parent.parent
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path): return json.loads(path.read_text())
packet = root / 'r21-pack'
manifest = read(packet / 'MANIFEST.json')['files']
for name, record in manifest.items():
    assert sha(packet / name) == record['sha256'] and (packet / name).stat().st_size == record['size'], name
pins = read(packet / 'SOURCE_PINS.json')
for name, blob in pins['reviewed_git_blobs'].items():
    actual = subprocess.check_output(['git', 'rev-parse', pins['reviewed_commit'] + ':' + name], cwd=root, text=True).strip()
    assert actual == blob, name
evidence = root / 'evidence/r21-pilot-a'
for name, expected in read(evidence / 'MANIFEST.json').items():
    assert sha(evidence / name) == expected, name
tools = root / 'tools'
source_hashes = {}
for path in sorted(tools.glob('*r21*')):
    if path.is_file():
        if path.suffix == '.py': ast.parse(path.read_text(), filename=str(path))
        source_hashes[path.name] = sha(path)
ex = 'docs/research/v8-no-work-100-20260907/experiments/'
circuit = root / 'evidence/r21-circuit-a'
for mode in ['helper', 'native']:
    staged = read(evidence / mode / 'r18-stage.json')['files']
    for name in ['r21_native.rs','r21_gkr.rs','r21_gkr_toy.rs','r21_trace_field.rs','r21_trace_main.rs','r21_pilot.rs','r21_sbf.rs']:
        assert source_hashes[name] == staged[ex + name], name
    assert sha(circuit / 'r21_circuit.rs') == staged[ex + 'r21_circuit.rs']
    for world in range(2):
        svm = evidence / mode / f'svm-world{world}'
        meta = read(svm / 'metadata.json')
        assert meta['driver_source_sha256'] == source_hashes['r21_svm_probe.rs']
        wire = evidence / 'helper' / f'host-world{world}/generated/helper.bin'
        assert sha(wire) == meta['wire_sha256']
        public = root / f'evidence/r21-source-a/public-world{world}.bin'
        assert wire.read_bytes()[:384] == public.read_bytes()
        context = evidence / 'helper' / f'host-world{world}/context.bin'
        assert wire.read_bytes()[400:432] == context.read_bytes()
        rows = [json.loads(line) for line in (svm / 'svm.jsonl').read_text().splitlines()]
        assert all(not r['complete_aspis_verifier'] and r['heap_bytes'] == 262144 for r in rows)
        assert all(not r['accepted'] for r in rows if r['case'] != 'honest')
fixture_hashes = [read(evidence / 'helper' / f'host-world{w}/metadata.json')['fixtures']['proof-1.bin'] for w in range(2)]
assert fixture_hashes[0] != fixture_hashes[1]
with tempfile.TemporaryDirectory(prefix='aspis-r21-circuit-check-') as temp:
    generated = Path(temp) / 'generated'
    subprocess.run([sys.executable, str(tools / 'generate_r21_layers.py'), '--dag', str(root / 'evidence/r21-source-a/source-dag.json'), '--output', str(generated)], check=True, stdout=subprocess.DEVNULL)
    for name in ['r21_circuit.rs','circuit.json','circuit-profile.json']:
        assert (generated / name).read_bytes() == (circuit / name).read_bytes(), name
receipt = read(evidence / 'pilot-receipt.json')
result = {'integrity': 'PASS', 'packet_files': len(manifest), 'git_blob_pins': len(pins['reviewed_git_blobs']),
    'circuit_regeneration': 'byte-identical', 'compiled_sources_match_local': True,
    'two_distinct_original_proofs': fixture_hashes, 'pilot_decision': receipt['decision'],
    'complete_aspis_gate_passed': False, 'security_theorem': False, 'tool_sha256': source_hashes}
if a.output:
    assert not a.output.exists()
    a.output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
