#!/usr/bin/env python3
"""Audit Z5 enumeration, C1 matrices, exact Z4c replay and final source hashes."""
import ast, hashlib, itertools, json, pathlib, re
here = pathlib.Path(__file__).resolve().parent
root = here.parents[3]
text = (here / 'probe-Z5.log').read_text()
old = (here / 'probe-C.log').read_text()
evidence = json.loads((here / 'evidence-Z5.json').read_text())
for file, digest in evidence['final_source_sha256'].items():
    assert hashlib.sha256((root / file).read_bytes()).hexdigest() == digest, file
for file, digest in evidence['decision_source_sha256'].items():
    assert hashlib.sha256((root / file).read_bytes()).hexdigest() == digest, file
ranks = {}
passes = []
failures = []
distribution = []
for line in text.splitlines():
    if line.startswith('Z5_RANKS '):
        m = re.fullmatch(r'Z5_RANKS label=(\S+) random=(\[.*?\]) consecutive=(\[.*?\]) pass=(true|false)', line)
        assert m, line
        row = {'random': ast.literal_eval(m[2]), 'consecutive': ast.literal_eval(m[3]), 'pass': m[4] == 'true'}
        assert len(row['random']) == len(row['consecutive']) == 16
        assert row['pass'] == all(r == 112 for r in row['random'] + row['consecutive'])
        assert m[1] not in ranks, m[1]
        ranks[m[1]] = row
    if line.startswith('Z5_PASS '):
        m = re.fullmatch(r'Z5_PASS ordinal=(\d+) stage=(\d+) index=(\d+) tau=(\[.*?\]) sigma=(.*)', line)
        assert m, line
        passes.append({'ordinal': int(m[1]), 'stage': int(m[2]), 'index': int(m[3]), 'tau': ast.literal_eval(m[4]), 'sigma': ast.literal_eval(m[5])})
    if line.startswith('Z5_FAILURE '):
        m = re.fullmatch(r'Z5_FAILURE ordinal=(\d+) stage=(\d+) index=(\d+) tau=(\[.*?\]) sigma=(.*?) first_trial=(\d+) first_set=(\w+) first_column=(\d+) first_rank=(\d+)', line)
        assert m, line
        failures.append(dict(ordinal=int(m[1]), stage=int(m[2]), index=int(m[3]), tau=ast.literal_eval(m[4]), sigma=ast.literal_eval(m[5]), first_trial=int(m[6]), first_set=m[7], first_column=int(m[8]), first_rank=int(m[9])))
    if line.startswith('Z5_DISTRIBUTION '):
        fields = dict(re.findall(r'(\w+)=(\w+)', line))
        distribution.append({k: v if k == 'first_set' else int(v) for k, v in fields.items()})
for i, candidate in enumerate(passes, 1):
    candidate['c1'] = [{'trial': t, **ranks[f'pass_{i}_trial_{t}']} for t in range(20)]
    assert all(row['pass'] for row in candidate['c1'])
for i, failure in enumerate(failures, 1):
    failure['ranks_at_first_failing_trial'] = ranks[f'failure_{i}']
    assert failure['first_rank'] == ranks[f'failure_{i}'][failure['first_set']][failure['first_column']]
    assert failure['first_rank'] < 112
search_done = re.findall(r'Z5_SEARCH_DONE checked=(\d+) passed=(\d+) failures=(\d+) wall_seconds=([\d.]+)', text)
assert len(search_done) == 1
checked, passed, rejected = map(int, search_done[0][:3])
assert passed == len(passes) and checked == passed + rejected
assert sum(row['count'] for row in distribution) == rejected
assert len(failures) == min(20, rejected)
assert [c['ordinal'] for c in passes] == sorted(c['ordinal'] for c in passes)
if all(c['stage'] == 1 for c in passes):
    enumeration = list(itertools.permutations(range(5)))
    for candidate in passes + failures:
        assert tuple(candidate['tau']) == enumeration[candidate['index']]
        assert candidate['ordinal'] == candidate['index'] + 1
        assert candidate['sigma'] == [[0, 1, 2, 3]] * 5
    assert checked == 120
assert 'Z5_AUDIT cached_rows_and_grouped_ranks_match_original=true' in text
old_ch = {int(re.search(r'trial=(\d+)', line)[1]): line for line in old.splitlines() if line.startswith('CHALLENGE ')}
old_ob = {(int(re.search(r'trial=(\d+)', line)[1]), int(re.search(r'pair=(\d+)', line)[1])): line for line in old.splitlines() if line.startswith('Z4B_REPLAY ')}
challenges = set()
replayed = set()
c1 = []
gates = []
results = []
for line in text.splitlines():
    if line.startswith('CHALLENGE '):
        t = int(re.search(r'trial=(\d+)', line)[1]); assert line == old_ch[t]; challenges.add(t)
    if line.startswith('Z4B_REPLAY '):
        key = (int(re.search(r'trial=(\d+)', line)[1]), int(re.search(r'pair=(\d+)', line)[1]))
        assert line == old_ob[key], key
        assert key not in replayed
        replayed.add(key)
    if line.startswith('C1_C '):
        m = re.fullmatch(r'C1_C trial=(\d+) pattern=(\w+) ranks=(\[.*\]) want_each=112', line)
        assert m, line
        c1.append(dict(trial=int(m[1]), pattern=m[2], ranks=ast.literal_eval(m[3])))
    if line.startswith('GATE_C '):
        fields = dict(re.findall(r'(\w+)=([^ ]+)', line))
        gates.append({key: int(fields[key]) for key in ['trial', 'silent_rank', 'initial_retained_rank', 'full_conditioned_rank', 'i_pass', 'ii_pass', 'attempted']})
    if line.startswith('RESULT '):
        head, support = line.split(' quotient_support='); support, pivots = support.split(' excess_pivots=')
        fields = dict(re.findall(r'(image_rank|targets|failures|excess_rank)=(\d+)', head))
        results.append({'label': head[7:].split(' image_rank=')[0], **{k: int(v) for k, v in fields.items()}, 'quotient_support': ast.literal_eval(support), 'excess_pivots': ast.literal_eval(pivots)})
stop = [line for line in text.splitlines() if line.startswith('STOP ')]
controls = {}
if passes:
    selected = re.findall(r'Z5_GATE tau=(\[.*?\]) sigma=(.*?) generic_trials=20 targets=100', text)
    assert len(selected) == 1
    assert ast.literal_eval(selected[0][0]) == passes[0]['tau']
    assert ast.literal_eval(selected[0][1]) == passes[0]['sigma']
    for name in ['identity', 'D13']:
        controls[name] = [{'trial': t, **ranks[f'control_{name}_trial_{t}']} for t in range(20)]
    assert all(row['pass'] for row in controls['D13'])
    if not stop:
        assert len(challenges) == 20 and len(replayed) == 100
        assert len(gates) == 20 and len(results) == 60 and len(c1) == 40
        assert all(row['ranks'] == [112]*16 for row in c1)
        assert 'Z4C_DONE trials=20 i_pass=100 ii_pass=100' in text
        assert all(row['i_pass'] == row['ii_pass'] == row['attempted'] == 5 for row in gates)
        assert all(row['silent_rank'] == 1076 for row in gates)
        assert all(row['failures'] == row['excess_rank'] == 0 and not row['quotient_support'] and not row['excess_pivots'] for row in results)
summary = dict(base_revision=evidence['base_revision'], computation_only=True,
    challenge_seed='0x5348f0b9a87835d0', search_seed='0x5a35d16120261010',
    search=dict(checked=checked, passed=passed, failed=rejected,
        order='lexicographic tau, then lexicographic sigma_0, then seeded Fisher-Yates',
        policy='finish first successful exhaustive stage; later stages not needed',
        completed_stages=[dict(stage=int(m[0]), tested=int(m[1])) for m in re.findall(r'Z5_STAGE_DONE stage=(\d+) tested=(\d+)', text)],
        passing_candidates=passes, first_20_failures=failures,
        first_failure_rank_distribution=distribution,
        rejection_order='challenge trial, first distinct eligible-row column group, consecutive then random',
        cache_audit='all 1024 balanced row observations and all 16 ranks equal original C1 loop for identity, D13, seeded random digit transport, on both fibre sets'),
    controls=controls, selected=passes[0] if passes else None,
    exact_Z4c_replayed_targets=len(replayed), compiled_source_hashes_verified=len(evidence['final_source_sha256']),
    decision_source_hashes_verified=len(evidence['decision_source_sha256']), stop=stop,
    aggregate=dict(challenges_completed=len(gates), attempted=sum(g['attempted'] for g in gates),
        i_pass=sum(g['i_pass'] for g in gates), ii_pass=sum(g['ii_pass'] for g in gates),
        silent_ranks=sorted(set(g['silent_rank'] for g in gates)),
        initial_retained_ranks=sorted(set(g['initial_retained_rank'] for g in gates)),
        full_conditioned_ranks=sorted(set(g['full_conditioned_rank'] for g in gates))),
    c1=c1, gates=gates, results=results)
(here / 'summary-Z5.json').write_text(json.dumps(summary, indent=2)+'\n')
print(json.dumps({key: summary[key] for key in ['compiled_source_hashes_verified', 'exact_Z4c_replayed_targets', 'stop', 'aggregate']}, indent=2))
