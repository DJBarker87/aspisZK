"""Read-only final source/receipt/hash audit. Does not submit Lean jobs."""
import hashlib, json, pathlib, re, subprocess
E=pathlib.Path(__file__).resolve().parent
R=E.parents[1]
L=R/'lean'
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
assert [r['attempt'] for r in receipts]==list(range(9588,9600))
assert all(r['dependencies_stable'] and r['swaps']==0 for r in receipts)
assert len({(r['source_sha256'],r['deps_fingerprint']) for r in receipts})==12
current={r['module']:r for r in receipts if r['exit']==0}
assert len(current)==4
paths={}; signatures={}; count=0
for module,r in current.items():
    p=L/f'{module}.lean'; s=p.read_text()
    assert sha(p)==r['source_sha256']
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b|set_option (maxRecDepth|maxHeartbeats)',s,re.M)
    names=re.findall(r'^theorem (\w+)',s,re.M)
    for name in names:
        assert f'#print axioms {name}' in s
        assert any(f'.{name}\'' in line for line in r['axioms'])
    count+=len(names)
    for line in r['axioms']:
        if 'depends on axioms:' in line:
            assert set(re.search(r'\[([^]]*)\]',line).group(1).replace(' ','').replace('\n','').split(',')) <= {'propext','Classical.choice','Quot.sound'}
        else: assert 'does not depend on any axioms' in line
    signatures[module]=names
    paths[f'sources/{module}.lean']=r['source_sha256']
    paths[f'objects/{module}.olean']=r['object']['sha256']
    for d in r['dependencies']:
        for sub,ext,key in [('sources','lean','source_sha256'),('objects','olean','object_sha256')]:
            path=f"{sub}/{d['module']}.{ext}"
            assert path not in paths or paths[path]==d[key]
            paths[path]=d[key]
    assert r['caps']==dict(lean_memory_mb=7000,MemoryHigh='5G',MemoryMax='7G',MemorySwapMax=0,TasksMax=128)
remote='import pathlib,hashlib,json\np=pathlib.Path("/home/dombarker/project-offloads/aspis-joint-20261019")\nexpected='+repr(paths)+'\nprint(json.dumps({k:hashlib.sha256((p/k).read_bytes()).hexdigest()==v for k,v in expected.items()}))\n'
checks=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=remote,text=True))
assert all(checks.values())
changes=subprocess.check_output(['git','diff','--name-status','cea53c19a'],text=True).splitlines()
assert all(line.startswith('A\t') for line in changes if '/lean/' in line)
result=dict(status='pass',baseline='cea53c19a',audited_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),modules=list(current),theorems=count,accepted_attempts=[r['attempt'] for r in receipts if r['exit']==0],failed_attempts=[r['attempt'] for r in receipts if r['exit']!=0],peak_rss_kib=max(r['peak_rss_kib'] for r in receipts),swaps=0,host_hashes_verified=len(checks),source_signatures=signatures,attempt_allocation_exhausted=True,sim_preparation_discharged=False,full_endpoint_created=False,whole_experiment_source_join='open named premise in retained endpoint')
(E/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
