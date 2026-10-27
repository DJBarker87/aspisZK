"""Check this read-only recount packet without rerunning Lean."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

E = Path(__file__).resolve().parent
R = E.parents[1]
start = 'eb7eab86b9e06595ce4e37a7f20fe44616d845e1'
receipts = [json.loads(p.read_text()) for p in sorted(E.glob('Rc11_*/receipt.json'))]
assert len(receipts) == 3
for d in receipts:
    assert d['exit_status'] == 0 and d['swaps'] == '0'
    assert d['limits'] == {'memory.high':'6442450944', 'memory.max':'8589934592',
                           'memory.swap.max':'0', 'pids.max':'64'}
    for module, digest in d['source_hashes'].items():
        assert hashlib.sha256((R/'lean'/module).read_bytes()).hexdigest() == digest
    for line in d['print_axioms']:
        if 'depends on axioms:' in line:
            names = line.split('depends on axioms: [', 1)[1].rstrip(']').split(', ')
            assert set(names) <= {'propext','Classical.choice','Quot.sound'}
for name in ['Rc11_Candidate','Rc11_Inventory','Rc11_Boundaries']:
    s = (R/'lean'/(name+'.lean')).read_text()
    assert not re.search(r'^\s*(?:theorem|lemma|axiom|def|abbrev|structure|instance)\b', s, re.M)
    assert not re.search(r'\b(?:sorry|admit|native_decide|maxHeartbeats|maxRecDepth)\b', s)
for name in ['BEFORE','AFTER']:
    s = (E/f'Rc11_{name}.lean.txt').read_text()
    assert '⋯' not in s and '...' not in s
p = json.loads((E/'Rc11_premises.json').read_text())
assert len(p['rows']) == 116 and p['added_atomic_rows'] == [] and p['reclassified'] == []
assert p['actual_delta'] == {'T':0,'P':-1,'G':0,'C':0}
assert p['deployment_inclusive_delta'] == {'T':0,'P':-2,'G':0,'C':0}
assert all(v == 0 for v in p['adopted_delta'].values())
changed = subprocess.check_output(['git','diff',start,'--name-only'],cwd=R,text=True).splitlines()
allowed = lambda path: (path.startswith('evidence/recount11-20261027/') or
    path in ['lean/Rc11_Candidate.lean','lean/Rc11_Inventory.lean','lean/Rc11_Boundaries.lean',
             'design/SECURITY-CONTRACT-ARX-AMENDMENT-DRAFT-20261027.md'])
assert all(allowed(path) for path in changed), changed
for path in ['design/PREMISE-LEDGER-20261025.md',
    'docs/research/100bit-spend-path-20261013/design/SECURITY-CONTRACT-20261021.md']:
    assert subprocess.check_output(['git','show',start+':'+path],cwd=R) == (R/path).read_bytes()
tracked = subprocess.check_output(['git','ls-files','evidence/recount11-20261027'],cwd=R,text=True).splitlines()
assert all(not x.endswith(('.olean','.ilean','.tar','.gz','.elf')) for x in tracked)
result = dict(status='pass', scope='Mechanical recount and definition draft, not adoption or release proof',
    branch=subprocess.check_output(['git','branch','--show-current'],cwd=R,text=True).strip(),
    lean_attempts=len(receipts), kani_runs=0,
    wall_seconds=sum(d['wall_seconds'] for d in receipts),
    peak_rss_kib=max(int(d['peak_rss_kib']) for d in receipts), swaps=0,
    standard_axioms_only=True, new_proofs=0, adopted_delta=0,
    changed_paths=changed, authoritative_ledger_and_contract_unchanged=True)
(E/'Rc11_validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
