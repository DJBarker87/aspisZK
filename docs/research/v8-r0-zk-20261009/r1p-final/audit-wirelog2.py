#!/usr/bin/env python3
"""Check the frozen two-module extension against focused env-J receipts."""
import hashlib, json, pathlib, re, shlex, subprocess
root=pathlib.Path(__file__).resolve().parents[1]
remote='dombarker@100.108.41.90'
j='/home/dombarker/project-offloads/aspis-joint-20261019'
modules=['R1Z/PhaseWireLog2Bin','R1Z/PrivacyR1HeadlineWire2']
rows=[json.loads(l) for l in (root/'r1p-final/wirelog2-attempts-9730-9799.jsonl').read_text().splitlines()]
assert all(9730 <= r['attempt'] <= 9799 for r in rows)
assert len({r['attempt'] for r in rows}) == len(rows)
paths=[f'{j}/sources/{m}.lean' for m in modules+['R1Z/PrivacyR1HeadlineAcct']]
paths += [f'{j}/objects/{m}.olean' for m in modules+['R1Z/PrivacyR1HeadlineAcct']]
script='''import hashlib,json,pathlib
print(json.dumps({p:dict(sha256=hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest(),size=pathlib.Path(p).stat().st_size) for p in PATHS}))
'''.replace('PATHS',repr(paths))
host=json.loads(subprocess.check_output(['ssh',remote,'python3 -c '+shlex.quote(script)],text=True))
entries=[]
for m in modules:
    src=root/'lean'/(m+'.lean'); text=src.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+max(RecDepth|Heartbeats)',text)
    sha=hashlib.sha256(src.read_bytes()).hexdigest()
    r=next(r for r in reversed(rows) if r['module']==m and r['source_sha256']==sha and r['exit']==0)
    assert host[f'{j}/sources/{m}.lean']['sha256']==sha
    assert r['swaps']=='0'
    axioms=re.findall(r"'([^']+)' (depends on axioms:\s*\[[\s\S]*?\]|does not depend on any axioms)",r['output'])
    required=re.findall(r'^#print axioms (\S+)',text,re.M)
    assert len(axioms)==len(required),(m,len(axioms),required)
    for name,ax in axioms:
        if 'depends on' in ax:
            names={n.strip() for n in ax[ax.index('[')+1:ax.index(']')].split(',') if n.strip()}
            assert names <= {'propext','Classical.choice','Quot.sound'},(name,names)
    for dep in r['dependency_objects']:
        sha_dep,path=dep.split(None,1)
        assert host[path]['sha256']==sha_dep,(m,path)
    entries.append(dict(module=m,source_sha256=sha,success_attempt=r['attempt'],
        deps_fingerprint=r['deps_fingerprint'],exit=r['exit'],wall=r['wall'],
        peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],axiom_reports=axioms,
        object=host[f'{j}/objects/{m}.olean']))
acct='R1Z/PrivacyR1HeadlineAcct'
assert hashlib.sha256((root/'lean'/(acct+'.lean')).read_bytes()).hexdigest()==host[f'{j}/sources/{acct}.lean']['sha256']
# Compare the two compiled theorem signatures in the endpoint, ignoring namespace.
s=(root/'lean/R1Z/PrivacyR1HeadlineWire2.lean').read_text()
sigs=re.findall(r'theorem privacy_headline_wire2\n[\s\S]*?(?= := by)',s)
assert len(sigs)==2
before,after=sigs
start=before.index('    (R_wire_D80_batches'); end=before.index('    (observer_program',start)
assert before[:start]+before[end:]==after
assert 'R_wire_D80_batches' not in after and 'R_wire_D80_ordered_log' not in after
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
result=dict(base_revision='8d47a08c3',source_stage_revision=revision,env='J',
    exact_targets=entries,signature_diff='only the two D80 binders deleted after explicit specialization',
    source_join='R1Z.PhaseWireLog2Bin.RustSerializationJoin',rust_join_proved=False,
    host_sources_and_dependency_objects_current=True,
    full_predecessor_manifest_replayed=False,
    reason='New two-module symbolic extension only; all predecessors unchanged. No unchanged compile rerun.',
    all_attempts=[{k:r[k] for k in ['attempt','module','source_sha256','source_revision','deps_fingerprint','exit','wall','peak_rss_kib','swaps']} for r in rows])
(root/'r1p-final/wirelog2-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='pass',targets=[e['module'] for e in entries],attempts=[e['success_attempt'] for e in entries],source_stage_revision=revision)))
