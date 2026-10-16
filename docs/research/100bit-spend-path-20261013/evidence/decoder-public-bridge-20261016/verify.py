#!/usr/bin/env python3
"""Read/hash final Decoder-to-Caller receipts; never run Lean or a build."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tarfile

base = Path(__file__).resolve().parent
repo = base.parents[4]
sha = lambda b: hashlib.sha256(b).hexdigest()
digest = lambda j: sha(json.dumps(j, sort_keys=True).encode())
m = json.loads((base / 'manifest.json').read_text())
archive = base / m['archive']
assert archive.stat().st_size == m['archive_bytes']
assert sha(archive.read_bytes()) == m['archive_sha256']
with tarfile.open(archive) as tf:
    members = tf.getmembers()
    assert all(x.isfile() or x.islnk() for x in members)
    assert len({x.name for x in members}) == len(members)
    f = {x.name: tf.extractfile(x).read() for x in members}
assert len(f) == m['archive_entries']
sums = dict((n, h) for h, n in
            (line.split('  ', 1) for line in f['SHA256SUMS'].decode().splitlines()))
assert set(sums) == set(f) - {'SHA256SUMS'}
for n, h in sums.items():
    assert sha(f[n]) == h, n

pins = m['adapter_pins']
assert json.loads(f['caller-adapted/provenance/adapter-pins.json']) == pins
assert sha(f['caller-adapted/provenance/Discriminant.lean']) == pins['backend_generator_sha256']
tool = repo / 'docs/research/100bit-spend-path-20261013/tools/decoder-public-discriminant-bridge.py'
assert tool.read_bytes() == f['caller-adapted/provenance/decoder-public-discriminant-bridge.py']
subprocess.run(['python3', str(tool), '--check'], check=True)
assert sha(f['proofs/sources/AspisR1TerminalDecoder/Types.lean']) == pins['original_sha256']
assert sha(f['caller-adapted/sources/AspisR1TerminalDecoder/Types.lean']) == pins['adapter_sha256']
for name in ('Funs', 'FunsExternal'):
    assert f[f'proofs/sources/AspisR1TerminalDecoder/{name}.lean'] == \
        f[f'caller-adapted/sources/AspisR1TerminalDecoder/{name}.lean']
for name in ('ExtractedTerminalDecoderSuccess', 'ExtractedDecoderWithdrawalSuccess',
             'DecoderPaymentDiscriminantAudit', 'TerminalDecoderGeneratedAudit'):
    assert f[f'proofs/sources/{name}.lean'] == f[f'caller-adapted/sources/{name}.lean']

snapshots = {
    'original': json.loads(f['proofs/runs/withdrawal-a/external-inputs.json']),
    'adapted': json.loads(f['caller-adapted/external-inputs-public.json']),
}
standard = {'propext', 'Classical.choice', 'Quot.sound'}
for space, modules in m['modules'].items():
    prefix = 'proofs' if space == 'original' else 'caller-adapted'
    snapshot = snapshots[space]
    assert snapshot['lean_version'] == '4.32.0'
    keys = {}
    def external_key(name):
        if name not in keys:
            x = snapshot['modules'][name]
            keys[name] = digest({'source': x['source_sha256'],
                                'objects': {s: o['sha256'] for s, o in x['objects'].items()},
                                'imports': {d: external_key(d) for d in x['imports']},
                                'runtime': snapshot['runtime_files']})
        return keys[name]
    for name, r in modules.items():
        assert json.loads(f[f'{prefix}/successful-targets/{name}.json']) == r
        rel = name.replace('.', '/')
        src = f[f'{prefix}/sources/{rel}.lean']
        assert sha(src) == r['key']['source_sha256']
        item = r['source_manifest_entry']
        if not item['source'].startswith('diagnostic/'):
            assert (repo / item['source']).read_bytes() == src, (space, name)
        assert r['exit_status'] == 0 and r['axioms']['passed']
        assert r['key']['runtime'] == snapshot['runtime_files']
        assert r['limits'] == {'memory.high': '6442450944',
                               'memory.max': '8589934592', 'memory.swap.max': '0'}
        assert r['process_swaps'] == 0 and r['cgroup_swap_current'] == '0'
        for suffix, obj in r['objects'].items():
            assert sha(f[f'{prefix}/objects/{rel}{suffix}']) == obj['sha256']
        for dep, value in r['key']['imports'].items():
            if dep in modules:
                prior = modules[dep]
                assert value == {'receipt_key': digest(prior['key']), 'objects': prior['objects']}
            else:
                assert value == {'closure_key': external_key(dep),
                                 'objects': snapshot['modules'][dep]['objects']}
        assert all(set(a['axioms']) <= standard for a in r['axioms']['reports'])

adapted = m['modules']['adapted']
assert sum(len(r['axioms']['reports']) for r in adapted.values()) == \
    m['adapted_standard_only_reports'] == 41
assert adapted['TerminalDecoderGeneratedAudit']['axioms']['requested_count'] == 16
assert adapted['ExtractedDecoderCallerBridge']['axioms']['requested_count'] == 11
assert adapted['ExtractedDecoderPublicBridge']['axioms']['requested_count'] == 6
assert m['modules']['original']['DecoderPaymentDiscriminantAudit']['axioms'] == \
    adapted['DecoderPaymentDiscriminantAudit']['axioms']
for module, attempt in [('ExtractedDecoderCallerBridge', 'bridges-a'),
                        ('ExtractedDecoderPublicBridge', 'bridges-a'),
                        ('TerminalDecoderGeneratedAudit', 'cone-a')]:
    log = f[f'caller-adapted/runs/{attempt}/{module}/lean.log'].decode()
    reports = [{'declaration': n, 'axioms': [a.strip() for a in v.split(',') if a.strip()]}
               for n, v in re.findall(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", log, re.S)]
    reports += [{'declaration': n, 'axioms': []} for n in
                re.findall(r"'([^']+)'\s+does not depend on any axioms", log)]
    assert reports == adapted[module]['axioms']['reports']
failed = m['joint_import_failure']
assert failed['exit_status'] == 1 and failed['axioms']['requested_count'] == 0
assert json.loads(f['caller/runs/joint-a/DecoderCallerJoint/receipt.json']) == failed
assert b"environment already contains 'instDiscriminantPoolV1PaymentStatementFormatErrorIsize'" \
    in f['caller/runs/joint-a/DecoderCallerJoint/lean.log']
old = json.loads((base / m['original_generated_evidence']).read_text())
assert old['rust_source_revision'] == m['rust_source_revision']
for name in ('AspisR1TerminalDecoder.Types', 'AspisR1TerminalDecoder.FunsExternal',
             'AspisR1TerminalDecoder.Funs'):
    r = m['modules']['original'][name]
    assert r['key']['source_sha256'] == old['modules'][name]['source_sha256']
    assert r['objects'] == old['modules'][name]['objects']
print(f'PASS: {len(f)} members; original generated cache preserved; exact naming inverse; '
      'same14-tag audit;41standard-only adapted reports; fixed-field actual decoder/public bridge. '
      'hs,transition binding and runtime preservation remain OPEN.')
