#!/usr/bin/env python3
"""Validate continuation 3 receipts and unchanged endpoint signatures. No replay."""
from pathlib import Path
import hashlib, json, re, subprocess
root = Path(__file__).resolve().parents[5]
base = root / 'docs/research/100bit-spend-path-20261013'
ev = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
rows = [r for r in json.loads((ev/'manifest.json').read_text())['attempts']
        if r['module'].endswith('C3')]
latest = {r['module']: r for r in rows}
assert len(latest) == 6
for r in rows:
    attempt = ev / (r['module']+'-'+str(r['attempt']))
    assert sha(attempt/'source.lean') == r['source_sha256']
    assert json.loads((attempt/'receipt.json').read_text()) == r
    for k in ['module','attempt','source_sha256','deps_fingerprint','exit','wall_seconds',
              'peak_rss_bytes','swaps','source_revision','axioms','errors']:
        assert k in r, (r['module'], k)
for module, r in latest.items():
    src = base / 'lean' / (module+'.lean')
    assert r['exit'] == 0 and r['swaps'] == 0
    assert sha(src) == r['source_sha256']
    for dep in r['direct_imports']:
        assert sha(Path(dep['path'])) == dep['sha256']
    names = re.findall(r'^theorem\s+(\w+)', src.read_text(), re.M)
    assert len(names) == len(r['axioms']), (module,names,r['axioms'])
    for name in names:
        assert '#print axioms '+name in src.read_text()
        assert any('.'+name+"'" in a for a in r['axioms'])
    for line in r['axioms']:
        ax = re.search(r'\[([^]]*)\]', line)
        if ax:
            assert set(x.strip() for x in ax[1].split(',')) <= {
                'propext','Classical.choice','Quot.sound'}
    source = re.sub(r'/-.*?-/', '', src.read_text(), flags=re.S)
    assert not re.search(r'\b(sorry|sorryAx|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)', source)
    assert not re.search(r'^\s*(?:by\s+)?admit\s*$', source, re.M)
# The previous continuation's Lean modules and the two headline sources stay unchanged.
lean_root = str((base/'lean').relative_to(root))
changes = subprocess.check_output(['git','diff','--name-status','1211847d4','--',lean_root],cwd=root,text=True)
for line in changes.splitlines():
    status,path = line.split('\t')
    assert status == 'A' and Path(path).name.startswith('OraclePort')
endpoints = []
for module in ['R1FinalSoundnessBinPerQueryR19','R1FinalSoundnessHeadline']:
    path = base/'lean'/(module+'.lean')
    before = subprocess.check_output(['git','show','1211847d4:'+str(path.relative_to(root))],cwd=root)
    assert before == path.read_bytes()
    endpoints.append({'module':module,'sha256':sha(path),'deletions':0})
(ev/'continuation3-existing-headline-signature.diff').write_text('')
# Published manifest lists frozen focused attempts; no unchanged Lean replay.
result = {
    'schema':'focused-extractor-proof-packet-v1',
    'scope':'Continuation 3 focused cached-object checks; not a coherent frozen release',
    'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
    'base_revision':'1211847d4',
    'attempt_count':len(rows),'failed_attempts':sum(r['exit'] != 0 for r in rows),
    'module_count':len(latest),'final_axiom_reports':sum(len(r['axioms']) for r in latest.values()),
    'peak_rss_bytes':max(r['peak_rss_bytes'] for r in rows),
    'swaps':sum(r['swaps'] or 0 for r in rows),
    'memory_cap_failures':[r['module']+'-'+str(r['attempt']) for r in rows if r['exit'] < 0],
    'endpoints':endpoints,'old_headline_premise_deletions':0,
    'proved':['reached ten-plus-twelve accumulator composition and ClosedSum equivalence',
              '66-leaf law including duplicates; 1040 batch / 1046 checkpoint-batch bound',
              'inherited parser cannot accept any bounded terminal message'],
    'blocked':['physical checkpoint prepared-field construction and parser-state join',
               'nonvacuous acceptance-to-typed-arithmetic transfer and completed dV headline'],
    'obstruction':'terminalBytes length <= 3717, parse requires length = 57607',
    'remaining':['separate stored-proof carrier and experiment/compiler/Pool accounting',
                 'selected typed arithmetic on the same compiled rows',
                 'Rust-equals-dV join and retained runtime/source/release boundaries',
                 'ledger adequacy on the larger Q+2322 log domain'],
    'final_attempts':[latest[m] for m in sorted(latest)],
    'all_attempts':rows,
}
(ev/'continuation3-manifest.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['all_attempts','final_attempts']},indent=2))
