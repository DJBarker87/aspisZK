#!/usr/bin/env python3
"""Compare fixed-width gamma code against the pinned complete tag-offset build."""
import contextlib, hashlib, io, json, re, runpy, subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
EX = ROOT / 'experiments'
EV = ROOT / 'evidence/gamma-fixed'
with contextlib.redirect_stdout(io.StringIO()):
    prior = runpy.run_path(str(EX / 'audit_tag_offsets.py'))
check, summary = prior['check'], prior['summary']
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
# Later research edits must not silently relabel this historical binary's
# source. Resolve the actual gamma-fixed checkpoint blob, not today's file.
query_source = subprocess.run(['git','show',
    '54303c98ef06ba8ea72d3456c738fcb51a362796:docs/research/v8-no-work-100-20260907/experiments/query_arithmetic.rs'],
    cwd=ROOT,check=True,capture_output=True).stdout
query_source_sha256 = hashlib.sha256(query_source).hexdigest()
assert query_source_sha256 == 'bb497d35e1e5538480d48efc6d376984378d9dc756bb8288f0d5731103c228c0'
def load(name, count):
    rows = {p.stem: check(json.loads(p.read_text())) for p in sorted((EV / name).glob('*.json'))}
    assert len(rows) == count, (name, len(rows))
    return rows
maximum = load('gamma-fixed-max-v1', 24)
ordinary = load('gamma-fixed-ordinary-v1', 24)
rollback = load('gamma-fixed-rollback-v1', 2)
ms = summary(maximum)
old = summary(prior['maximum'])
savings = {}
for shape, xs in ms['shapes'].items():
    bs = old['shapes'][shape]
    assert [x['proof_sha256'] for x in xs] == [x['proof_sha256'] for x in bs]
    assert all(x['body'] == 40282 for x in xs)
    savings[shape] = [a['cu'] - b['cu'] for a, b in zip(bs, xs)]
for rows, before in ((maximum, prior['maximum']), (ordinary, prior['ordinary']), (rollback, prior['rollback'])):
    for key, x in rows.items():
        assert x['execution']['txv1_declared_compute_unit_limit'] == 1200000
        assert x['artifacts']['selected_verifier']['sha256'] == ms['artifact_hashes']['selected_verifier']
        assert x['fixture']['proof_sha256'] == before[key]['fixture']['proof_sha256']
        for role in ('pool', 'registry', 'token_program'):
            assert x['artifacts'][role] == before[key]['artifacts'][role]
        for field in ('outcome', 'error'):
            assert x['execution'][field] == before[key]['execution'][field]
        if rows is not rollback:
            assert x['artifacts']['token_program']['explicit_pinned_sbf_control']['variant'] == 'legacy35'
        else:
            assert x['execution']['selected_verifier_cpi_observed_in_logs']
            assert x['scenario'] == 'withdrawal-cpi-failure'

lean = (EX / 'gamma-fixed-final-lean.log').read_text()
assert 'error:' not in lean and 'sorryAx' not in lean
assert sha(EX / 'GammaDotUnroll.lean') in lean
oleans = re.findall(r'([a-f0-9]{64})\s+[^\n]+\.olean', lean)
assert len(oleans) == 2
if (EX / 'GammaDotUnroll.olean').exists(): assert sha(EX / 'GammaDotUnroll.olean') == oleans[-1]
axioms = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", lean)
assert len(axioms) == 4
assert all(set(a.split(', ')) <= {'propext', 'Classical.choice', 'Quot.sound'} for _, a in axioms)
resources = {}
for name in ('host-build', 'host-test', 'sbf-build'):
    path = EV / f'gamma-fixed-{name}.log'
    log = path.read_text()
    assert '\tExit status: 0' in log
    assert not re.search(r'Stack offset .* exceeded|error:', log)
    wall = re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)', log)[1]
    parts = list(map(float, wall.split(':')))
    resources[name] = {'exit': 0,
        'wall_seconds': sum(v*60**i for i,v in enumerate(reversed(parts))),
        'rss_kib': int(re.search(r'Maximum resident set size \(kbytes\): (\d+)', log)[1]),
        'swaps': int(re.search(r'Swaps: (\d+)', log)[1]), 'log': str(path.relative_to(ROOT))}
    assert resources[name]['swaps'] == 0
assert 'canonical_profiles=512 maximal_limb_dot=true noncanonical_positions=152 short_inputs=2' in (EV/'gamma-fixed-host-test.log').read_text()
failed = []
for name, reason in (
        ('gamma-fixed-lean.log', 'Runner required -R for output outside cached workspace'),
        ('gamma-fixed-checked-lean.log', 'Rewrite matching of function composition; fixed by direct equality transitivity')):
    log = (EX / name).read_text()
    failed.append({'log': f'experiments/{name}', 'exit': 1, 'reason': reason,
        'retained_claimed_proof': False,
        'wall_seconds': float(re.search(r'([\d.]+) real', log)[1]),
        'rss_bytes': int(re.search(r'(\d+)  maximum resident set size', log)[1]),
        'swaps': int(re.search(r'(\d+)  swaps', log)[1])})

raw = maximum['withdrawal-255-2-success']
out = {'schema': 'aspis.research.gamma-fixed.v1',
    'base_revision': 'b062f8ffa2efdc7c21312432530745df66bea5fa',
    'maximum': ms, 'ordinary': summary(ordinary), 'rollback_cases': len(rollback),
    'same_proof_savings_cu': savings,
    'worst_observed_cu': max(x['cu'] for xs in ms['shapes'].values() for x in xs),
    'lean': {'source': 'experiments/GammaDotUnroll.lean', 'source_sha256': sha(EX/'GammaDotUnroll.lean'),
        'olean_sha256': oleans[-1], 'exit': 0,
        'wall_seconds': float(re.search(r'([\d.]+) real', lean)[1]),
        'rss_bytes': int(re.search(r'(\d+)  maximum resident set size', lean)[1]),
        'swaps': int(re.search(r'(\d+)  swaps', lean)[1]), 'axioms': dict(axioms),
        'log': 'experiments/gamma-fixed-final-lean.log'},
    'failed_lean_preflights': failed, 'resources': resources,
    'query_source_sha256': query_source_sha256,
    'artifacts': {role: raw['artifacts'][role] for role in ('selected_verifier','pool','registry','token_program')},
    'elf_delta_bytes': raw['artifacts']['selected_verifier']['bytes'] - prior['maximum']['withdrawal-255-2-success']['artifacts']['selected_verifier']['bytes'],
    'body_maximum': 697*16+52+24+22*621+2*296*26,
    'new_proof_or_transcript_bytes': 0, 'extra_heap_bytes': 0,
    'global_security_certificate': None, 'universal_cu_bound': None, 'grinding_credit_bits': 0,
    'scope': 'Exact seven-chunk summation/range model, unchanged chunk/reducer obligations, actual Rust differentials and complete SBF measurements; not a translated Rust or universal acceptance proof.'}
out['margin_to_1200000'] = 1200000-out['worst_observed_cu']
out['excess_over_same_pool_v7'] = {s: max(x['cu'] for x in xs) - prior['prior']['prior']['v7'][s][0]['cu']
    for s,xs in ms['shapes'].items()}
assert all(v > 0 for xs in savings.values() for v in xs)
print(json.dumps(out, indent=2))
