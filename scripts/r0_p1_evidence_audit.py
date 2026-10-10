#!/usr/bin/env python3
"""Read retained P1 evidence and check two small field witnesses; no reruns."""
import hashlib
import json
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parent.parent
out = root / 'results/r0-cost-probe-20261009'
base = 'f1e5ca9de668110f80c548abe5e80b43f838099f'


def read(name):
    return json.loads((out / name).read_text())


def write(name, value):
    (out / name).write_text(json.dumps(value, indent=2) + '\n')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


# Independent integer polynomial multiplication, without the Rust field code.
# Basis: 1,i,u,iu,v,iv,uv,iuv; i^2=-1, u^2=2+i, v^2=u.
P = 2**31 - 1


def multiply(a, b):
    c = [0] * 8
    for j, x in enumerate(a):
        for k, y in enumerate(b):
            i = (j & 1) + (k & 1)
            v = (j >> 2) + (k >> 2)
            u = ((j >> 1) & 1) + ((k >> 1) & 1) + v // 2
            terms = [(i, 2), (i + 1, 1)] if u >= 2 else [(i, 1)]
            for exponent, scale in terms:
                index = exponent % 2 + 2 * (u % 2) + 4 * (v % 2)
                c[index] += (-1)**(exponent // 2) * scale * x * y
    return [n % P for n in c]


witnesses = []
for variant in ['transfer', 'withdrawal']:
    name = f'c5-narrow-{variant}-observation.json'
    d = read(name)
    z = [0] * 8
    for coefficient in reversed(d['first_four_quotient_coefficients']):
        z = [(a + b) % P for a, b in zip(multiply(z, d['alpha_k']), coefficient)]
    assert z == d['first_fold_coefficient']
    assert any(z[4:]) and d['k_alpha_fold_coefficients_with_nonzero_high_k'] == 256
    assert d['same_row30_block'] and d['retained_c3_proof_bytes_equal']
    witnesses.append(dict(variant=variant, observation_sha256=sha(out / name),
                          integer_polynomial_recheck=True, coefficient=z,
                          high_k_nonzero=True))
write('c5-independent-witness.json', dict(method='integer polynomial Horner evaluation of coefficient zero', witnesses=witnesses))

checks = []
for stage in ['c0', 'c1', 'c2', 'c3']:
    for job in ['native', 'sbf', 'stack']:
        assert read(f'{stage}-{job}.json')['exit_status'] == 0
    corpus = read(f'{stage}-fixtures/corruption-cases.json')
    assert len(corpus) == 1894 and all(r['rejection'] != 'Ok(())' for r in corpus)
    stack = read(f'{stage}-stack/stack-audit.json')
    assert not stack['reachable_diagnostics']
    assert stack['text_sha256']['linked'] == stack['text_sha256']['measured']
    elf = sha(out / f'{stage}-elf/aspis_verifier.so')
    assert elf == stack['measured_elf_sha256']
    for variant in ['transfer', 'withdrawal']:
        proof = out / f'{stage}-fixtures/{variant}.proof.bin'
        public = out / f'{stage}-fixtures/{variant}.public.bin'
        fixture = read(f'{stage}-fixtures/{variant}.fixture.json')
        assert fixture['strict_native_accepted'] and fixture['release']
        diagnostic = read(f'{stage}-diagnostic/{variant}-diagnostic-1.json')
        assert diagnostic['verifier_completed'] and diagnostic['execution']['error'] is None
        assert diagnostic['sbf_heap_high_water_bytes'] <= 256 * 1024
        runs = list((out / f'{stage}-acceptance').glob(f'{variant}-run-*.json'))
        assert len(runs) == 5
        for run in runs + [out / f'{stage}-diagnostic/{variant}-diagnostic-1.json']:
            d = json.loads(run.read_text())
            assert d['elf_sha256'] == elf
            assert d['proof_sha256'] == sha(proof) and d['public_sha256'] == sha(public)
            if run in runs:
                assert d['runtime']['limit_cu'] == 1400000 and not d['verifier_completed']
                assert d['phase_markers'][-1]['phase'] == 'parsed'
                assert 'exceeded CUs meter' in '\n'.join(d['execution']['logs'])
        checks.append(dict(configuration=stage, variant=variant, native_accepted=True,
                           rejection_count=len(corpus), acceptance_runs=5,
                           acceptance_completions=0, diagnostic_completed=True,
                           heap_bytes=diagnostic['sbf_heap_high_water_bytes'],
                           reachable_stack_diagnostics=0, elf_sha256=elf))

resources = []
for path in sorted(out.glob('*.json')):
    d = json.loads(path.read_text())
    if isinstance(d, dict) and d.get('schema') == 'aspis.v8-state-only-cu.resources.v1':
        assert d['caps'] == {'memory.high': str(4 * 2**30), 'memory.max': str(6 * 2**30), 'memory.swap.max': '0'}
        assert d['cgroup_swap_current_bytes'] == 0 and d['stop_reason'] is None
        resources.append(dict(evidence=path.name, **d))
write('resources.json', resources)
write('evidence-audit.json', dict(measurements=checks, scopes=len(resources),
      peak_aggregate_rss_bytes=max(d['peak_aggregate_rss_bytes_sampled'] for d in resources),
      peak_cgroup_memory_bytes=max(d['cgroup_memory_peak_bytes'] for d in resources),
      swap_bytes=0, failed_jobs=[d['evidence'] for d in resources if d['exit_status'] != 0],
      c4_reuses_c3=True, c5_stop='K alpha leaves 256 non-K folded coefficients on each fixture'))

entries = subprocess.check_output(['git', 'ls-tree', '-r', base], cwd=root, text=True).splitlines()
protected = []
for entry in entries:
    metadata, name = entry.split('\t', 1)
    object_id = metadata.split()[2]
    if (name.endswith('.lean') or name.startswith('crates/aspis-core/src/r0/')
            or name == 'crates/aspis-prover/src/r0.rs'
            or 'fixture' in name.lower()):
        path = root / name
        assert path.is_file(), name
        contents = path.read_bytes()
        blob = b'blob ' + str(len(contents)).encode() + b'\0' + contents
        assert hashlib.sha1(blob).hexdigest() == object_id, name
        protected.append(dict(path=name, sha256=sha(path)))
write('preservation.json', dict(base=base, checked_files=len(protected), all_byte_equal=True, files=protected))
print(json.dumps(read('evidence-audit.json'), indent=2))
