#!/usr/bin/env python3
"""Audit measured complete transactions and the fixed-offset proof/code plan."""
import contextlib, hashlib, io, json, re, runpy
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EX = ROOT / 'experiments'
EVIDENCE = ROOT / 'evidence/tag-offset'
with contextlib.redirect_stdout(io.StringIO()):
    prior = runpy.run_path(str(EX / 'audit_tag_shared.py'))
check, summary = prior['check'], prior['summary']

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load(name, count):
    rows = {p.stem: check(json.loads(p.read_text()))
            for p in sorted((EVIDENCE / name).glob('*.json'))}
    assert len(rows) == count, (name, len(rows))
    assert all(x['execution']['txv1_declared_compute_unit_limit'] == 1200000
               for x in rows.values())
    return rows

maximum = load('tag-offset-max-v1', 24)
ordinary = load('tag-offset-ordinary-v1', 24)
rollback = load('tag-offset-rollback-v1', 2)
profile = next(iter(load('tag-offset-profile-v1', 1).values()))
ms = summary(maximum)
savings = {}
for shape, values in ms['shapes'].items():
    baseline = summary(prior['maximum'])['shapes'][shape]
    assert [v['proof_sha256'] for v in values] == [v['proof_sha256'] for v in baseline]
    assert all(v['body'] == 40282 for v in values)
    savings[shape] = [a['cu'] - b['cu'] for a, b in zip(baseline, values)]
for rows, baseline in ((maximum, prior['maximum']), (ordinary, prior['ordinary'])):
    for key, x in rows.items():
        for role in ('pool', 'registry', 'token_program'):
            assert x['artifacts'][role] == baseline[key]['artifacts'][role]
        assert x['artifacts']['token_program']['explicit_pinned_sbf_control']['variant'] == 'legacy35'
        for field in ('outcome', 'error'):
            assert x['execution'][field] == baseline[key]['execution'][field]
        assert x['fixture']['proof_sha256'] == baseline[key]['fixture']['proof_sha256']
for x in rollback.values():
    assert x['execution']['selected_verifier_cpi_observed_in_logs']
    assert x['scenario'] == 'withdrawal-cpi-failure'
for rows in (maximum, ordinary, rollback):
    assert all(x['artifacts']['selected_verifier']['sha256'] ==
               ms['artifact_hashes']['selected_verifier'] for x in rows.values())

leaves = []
for stem, logname, expected in (
        ('CopyTagOffsetModel', 'tag-offset-model-lean.log', 5),
        ('CopyTagOffsetPlans', 'tag-offset-plans-checked-lean.log', 32)):
    path = EX / logname
    log = path.read_text()
    assert 'error:' not in log and 'sorryAx' not in log
    assert sha(EX / f'{stem}.lean') in log
    oleans = re.findall(r'([a-f0-9]{64})\s+[^\n]+\.olean', log)
    assert len(oleans) == 2
    if (EX / f'{stem}.olean').exists():
        assert sha(EX / f'{stem}.olean') == oleans[-1]
    axioms = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log)
    assert len(axioms) == expected
    assert all(set(a.split(', ')) <= {'propext', 'Classical.choice', 'Quot.sound'}
               for _, a in axioms)
    free = re.findall(r"'([^']+)' does not depend on any axioms", log)
    assert len(free) == (1 if stem == 'CopyTagOffsetModel' else 0)
    leaves.append({'source': f'experiments/{stem}.lean', 'source_sha256': sha(EX / f'{stem}.lean'),
        'olean_sha256': oleans[-1], 'exit': 0,
        'wall_seconds': float(re.search(r'([\d.]+) real', log)[1]),
        'rss_bytes': int(re.search(r'(\d+)  maximum resident set size', log)[1]),
        'swaps': int(re.search(r'(\d+)  swaps', log)[1]),
        'axioms': dict(axioms), 'axiom_free': free, 'log': str(path.relative_to(ROOT))})

resources = {}
for name in ('test', 'sbf-build', 'profile-build'):
    path = EVIDENCE / f'tag-offset-{name}.log'
    log = path.read_text()
    assert '\tExit status: 0' in log
    assert not re.search(r'Stack offset .* exceeded|error:', log)
    wall = re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)', log)[1]
    parts = list(map(float, wall.split(':')))
    resources[name] = {'exit': 0,
        'wall_seconds': sum(x * 60**i for i, x in enumerate(reversed(parts))),
        'rss_kib': int(re.search(r'Maximum resident set size \(kbytes\): (\d+)', log)[1]),
        'swaps': int(re.search(r'Swaps: (\d+)', log)[1]), 'log': str(path.relative_to(ROOT))}
    assert resources[name]['swaps'] == 0

# Failed local preflights are diagnostics, not retained proof successes.
failed = []
for name, reason in (
        ('tag-offset-plans-lean.log', 'Fin coefficient normalization and exhaustive selector syntax'),
        ('tag-offset-plans-final-lean.log', 'Fin index syntax left distinct atoms to ring')):
    log = (EX / name).read_text()
    assert 'error:' in log
    failed.append({'log': f'experiments/{name}', 'exit': 1, 'reason': reason,
        'retained_claimed_proof': False,
        'wall_seconds': float(re.search(r'([\d.]+) real', log)[1]),
        'rss_bytes': int(re.search(r'(\d+)  maximum resident set size', log)[1]),
        'swaps': int(re.search(r'(\d+)  swaps', log)[1])})

raw = maximum['withdrawal-255-2-success']
assert profile['fixture']['proof_sha256'] == raw['fixture']['proof_sha256']
for role in ('pool', 'registry', 'token_program'):
    assert profile['artifacts'][role] == raw['artifacts'][role]
points = []
logs = profile['execution']['logs']
for i, line in enumerate(logs):
    if line.startswith('Program log: v8:'):
        match = re.fullmatch(r'Program consumption: (\d+) units remaining', logs[i + 1])
        assert match
        points.append((line.removeprefix('Program log: '), int(match[1])))
assert len(points) == 27
intervals = [{'from': a, 'to': b, 'cu': va - vb}
             for (a, va), (b, vb) in zip(points, points[1:])]

prep = (EVIDENCE / 'tag-offset-prepare.log').read_text()
hashes = re.findall(r'([a-f0-9]{64})\s+[^\n]+\.rs', prep)
assert len(hashes) == 2 and hashes[-1] == sha(EX / 'copy_tag_offsets_generated.rs')
plan = json.loads((EX / 'copy-tag-offset-plan.json').read_text())
old_elf = prior['maximum']['withdrawal-255-2-success']['artifacts']['selected_verifier']['bytes']
out = {'schema': 'aspis.research.tag-offset.v1',
    'base_revision': '623a01027e88d3324c8e9e7969b28505a8947fa6',
    'maximum': ms, 'ordinary': summary(ordinary), 'rollback_cases': len(rollback),
    'same_proof_savings_cu': savings,
    'worst_observed_cu': max(x['cu'] for xs in ms['shapes'].values() for x in xs),
    'lean': leaves, 'failed_lean_preflights': failed, 'resources': resources,
    'generator_sha256': sha(EX / 'generate_tag_offsets.py'),
    'copy_source_sha256': hashes[0], 'generated_rust_sha256': hashes[1],
    'plan': {k: v for k, v in plan.items() if k not in ('literal', 'emitted')},
    'artifacts': {role: raw['artifacts'][role] for role in ('selected_verifier', 'pool', 'registry', 'token_program')},
    'elf_growth_bytes': raw['artifacts']['selected_verifier']['bytes'] - old_elf,
    'profile': {'log': 'evidence/tag-offset/tag-offset-profile-v1/withdrawal-255-2.json',
        'proof_sha256': profile['fixture']['proof_sha256'],
        'verifier': profile['artifacts']['selected_verifier'],
        'total_cu_including_instrumentation': profile['execution']['compute_units'],
        'intervals_include_logging_and_codegen_effects': intervals},
    'body_maximum': 697*16 + 52 + 24 + 22*621 + 2*296*26,
    'new_proof_or_transcript_bytes': 0, 'extra_heap_bytes': 0,
    'global_security_certificate': None, 'universal_cu_bound': None, 'grinding_credit_bits': 0,
    'scope': 'Universal plan/integer/word-model equivalence; literal actual Rust differentials and complete SBF executions. Not a translated-source/compiler proof.'}
out['margin_to_1200000'] = 1200000 - out['worst_observed_cu']
out['excess_over_same_pool_v7'] = {s: max(x['cu'] for x in xs) - prior['prior']['v7'][s][0]['cu']
    for s, xs in ms['shapes'].items()}
assert all(n == 6007 for xs in savings.values() for n in xs)
assert out['body_maximum'] == 40282
print(json.dumps(out, indent=2))
