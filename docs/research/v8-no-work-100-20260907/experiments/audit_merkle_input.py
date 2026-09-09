#!/usr/bin/env python3
"""Audit complete Merkle implementation controls, not summed microbenchmarks."""
import contextlib, hashlib, io, json, re, runpy
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
EX = ROOT/'experiments'
EV = ROOT/'evidence/merkle-input'
with contextlib.redirect_stdout(io.StringIO()):
    prior = runpy.run_path(str(EX/'audit_gamma_fixed.py'))
check, summary = prior['check'], prior['summary']
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(name, count):
    rows = {p.stem: check(json.loads(p.read_text())) for p in sorted((EV/name).glob('*.json'))}
    assert len(rows) == count, (name, len(rows))
    assert all(x['execution']['txv1_declared_compute_unit_limit'] == 1200000 for x in rows.values())
    return rows
base = prior['maximum']
bs = summary(base)
variants = {}
sets = {}
for mode in ('slices', 'borrow', 'both'):
    rows = load(f'merkle-{mode}-max-v1', 24)
    sets[mode] = rows
    s = summary(rows)
    deltas = {}
    for shape, xs in s['shapes'].items():
        ys = bs['shapes'][shape]
        assert [x['proof_sha256'] for x in xs] == [y['proof_sha256'] for y in ys]
        assert all(x['body'] == 40282 for x in xs)
        deltas[shape] = [y['cu'] - x['cu'] for x, y in zip(xs, ys)]
    for key, x in rows.items():
        for role in ('pool', 'registry', 'token_program'):
            assert x['artifacts'][role] == base[key]['artifacts'][role]
        for field in ('outcome', 'error'):
            assert x['execution'][field] == base[key]['execution'][field]
    raw = rows['withdrawal-255-2-success']
    variants[mode] = {'maximum': s, 'same_proof_savings_cu': deltas,
        'worst_observed_cu': max(x['cu'] for xs in s['shapes'].values() for x in xs),
        'verifier': raw['artifacts']['selected_verifier'],
        'elf_delta_bytes': raw['artifacts']['selected_verifier']['bytes'] -
            base['withdrawal-255-2-success']['artifacts']['selected_verifier']['bytes']}
    assert all(v > 0 for xs in deltas.values() for v in xs)
for shape, xs in variants['both']['maximum']['shapes'].items():
    for mode in ('slices', 'borrow'):
        assert all(x['cu'] < y['cu'] for x,y in zip(xs, variants[mode]['maximum']['shapes'][shape]))

ordinary = load('merkle-both-ordinary-v1',24)
rollback = load('merkle-both-rollback-v1',2)
for rows, before in ((ordinary, prior['ordinary']), (rollback, prior['rollback'])):
    for key, x in rows.items():
        assert x['artifacts']['selected_verifier']['sha256'] == variants['both']['verifier']['sha256']
        assert x['fixture']['proof_sha256'] == before[key]['fixture']['proof_sha256']
        for role in ('pool','registry','token_program'):
            assert x['artifacts'][role] == before[key]['artifacts'][role]
        for field in ('outcome','error'):
            assert x['execution'][field] == before[key]['execution'][field]
        if rows is rollback:
            assert x['scenario'] == 'withdrawal-cpi-failure'
            assert x['execution']['selected_verifier_cpi_observed_in_logs']

resources = {}
for mode in ('slices','borrow','both'):
    for job in ('test','sbf-build'):
        path=EV/f'merkle-{mode}-{job}.log'; log=path.read_text()
        assert '\tExit status: 0' in log
        assert not re.search(r'Stack offset .* exceeded|error:', log)
        if job == 'test': assert '4 passed; 0 failed' in log
        wall=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log)[1]
        parts=list(map(float,wall.split(':')))
        resources[f'{mode}-{job}']={'exit':0,
            'wall_seconds':sum(x*60**i for i,x in enumerate(reversed(parts))),
            'rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log)[1]),
            'swaps':int(re.search(r'Swaps: (\d+)',log)[1]),'log':str(path.relative_to(ROOT))}
        assert resources[f'{mode}-{job}']['swaps'] == 0
lean=(EX/'merkle-input-symbolic-lean.log').read_text()
assert 'error:' not in lean and 'sorryAx' not in lean
assert sha(EX/'MerkleInput.lean') in lean
oleans=re.findall(r'([a-f0-9]{64})\s+[^\n]+\.olean',lean)
assert len(oleans)==2
if (EX/'MerkleInput.olean').exists(): assert sha(EX/'MerkleInput.olean') == oleans[-1]
axs=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",lean)
assert len(axs)==4
assert all(set(a.split(', ')) <= {'propext','Classical.choice','Quot.sound'} for _,a in axs)
failed=(EX/'merkle-input-lean.log').read_text()
assert 'error:' in failed
prep=(EV/'merkle-input-prepare.log').read_text()
hashes=re.findall(r'([a-f0-9]{64})\s+[^\n]+\.rs',prep)
assert len(hashes)==2 and hashes[-1]==sha(EX/'merkle_input_tests.rs')
raw=sets['both']['withdrawal-255-2-success']
out={'schema':'aspis.research.merkle-input.v1',
    'base_revision':'54303c98ef06ba8ea72d3456c738fcb51a362796',
    'variants':variants,'selected':'both','ordinary':summary(ordinary),'rollback_cases':len(rollback),
    'lean':{'source':'experiments/MerkleInput.lean','source_sha256':sha(EX/'MerkleInput.lean'),
        'olean_sha256':oleans[-1],'exit':0,'wall_seconds':float(re.search(r'([\d.]+) real',lean)[1]),
        'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',lean)[1]),
        'swaps':int(re.search(r'(\d+)  swaps',lean)[1]),'axioms':dict(axs),
        'log':'experiments/merkle-input-symbolic-lean.log'},
    'failed_preflight':{'exit':1,'log':'experiments/merkle-input-lean.log',
        'reason':'Broad simp expanded 53 concrete cells before append rewriting; replaced by symbolic append rewrites.',
        'wall_seconds':float(re.search(r'([\d.]+) real',failed)[1]),
        'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',failed)[1]),
        'swaps':int(re.search(r'(\d+)  swaps',failed)[1]),'retained_claimed_proof':False},
    'resources':resources,'merkle_source_sha256':hashes[0],'test_source_sha256':hashes[1],
    'artifacts':{role:raw['artifacts'][role] for role in ('selected_verifier','pool','registry','token_program')},
    'hash_model':{'parent_bytes':53,'internal_hashes_maximum_body':634,'prior_slice_lengths':[53],
        'new_slice_lengths':[1,26,26],'old_hash_syscall_cu':111,'new_hash_syscall_cu':121,
        'maximum_body_syscall_delta_cu':6340,'primitive_changed':False,
        'condition':'Hash backend hashes concatenation, not segment framing; source audited for pinned SHA backends.'},
    'body_maximum':697*16+52+24+22*621+2*296*26,'new_proof_or_transcript_bytes':0,
    'extra_heap_bytes':0,'grinding_credit_bits':0,'global_security_certificate':None,'universal_cu_bound':None,
    'scope':'Kernel-checked byte-input equality for flat-string hashes; borrowed traversal source audit and Rust tests; complete SBF measurements, not translated Rust/compiler equivalence.'}
out['worst_observed_cu']=variants['both']['worst_observed_cu']
out['margin_to_1200000']=1200000-out['worst_observed_cu']
out['excess_over_same_pool_v7']={s:max(x['cu'] for x in xs) -
    (max(x['cu'] for x in bs['shapes'][s])-prior['out']['excess_over_same_pool_v7'][s])
    for s,xs in variants['both']['maximum']['shapes'].items()}
print(json.dumps(out,indent=2))
