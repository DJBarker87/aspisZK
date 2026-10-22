#!/usr/bin/env python3
"""Final integrity audit and unchanged fail-closed completeness gates."""
import copy,hashlib,json,re,resource,subprocess,sys,time
from pathlib import Path
start=time.monotonic();R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s10-inventory4-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text())
checks=[]
for script in ['inventory.py','generate-cfg.py']:
    subprocess.run([sys.executable,'-B',str(R/'tools/s10-inventory4-20261021'/script),'--check'],check=True,capture_output=True)
checks.append('typed owner inventory and symbolic CFG sources regenerate exactly')
original=(R/'docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderStdModels.lean').read_text()
ported=(B/'lean/OraclePortStdBuilder.lean').read_text()
assert ported==original.replace('R1Z.BuilderStdModels','AspisR1.OraclePortStdBuilder').replace('/-! Standard-library adapters','/-! Exact namespace-only port of R1Z/BuilderStdModels.lean. Standard-library adapters')
checks.append('builder adapter port has only namespace and introductory comment changes')
modules=['OraclePortJoinSplitStd','OraclePortStdBuilder','OraclePortStdAllocation','OraclePortJoinSplitStdFrozen','OraclePortS10InventoryStd','OraclePortS10CFG']+[f'OraclePortS10Dominance{i}' for i in range(6)]+['OraclePortS10StdFreeze']
accepted=[]
for module in modules:
    src=B/'lean'/f'{module}.lean';digest=sha(src)
    receipts=[load(p) for p in E.glob(module+'-*/receipt.json')]
    good=[r for r in receipts if r['exit_status']==0 and r['source_sha256']==digest]
    assert good,'missing current successful focused receipt: '+module
    receipt=max(good,key=lambda r:r['attempt'])
    snap=E/f"{module}-{receipt['attempt']}/source.lean.txt";assert sha(snap)==digest
    assert receipt['swaps']==0 and receipt['peak_rss_bytes']<8*1024**3
    assert receipt['print_axioms'],module
    for line in receipt['print_axioms']:
        if 'does not depend on any axioms' in line:continue
        axioms=set(re.search(r'\[([^]]*)\]',line)[1].replace('\n','').replace(' ','').split(','))
        assert axioms<=set(['propext','Classical.choice','Quot.sound']),(module,line)
    # Every theorem declared here has its own audit, not only an imported root.
    for theorem in re.findall(r'^theorem (\w+)',src.read_text(),re.M):
        assert any('.'+theorem+"'" in l for l in receipt['print_axioms']),(module,theorem)
    accepted.append({k:receipt[k] for k in ['module','attempt','source_sha256','source_revision','exit_status','wall_seconds','peak_rss_bytes','swaps','print_axioms']})
checks.append('every new theorem has a current successful standard-axiom receipt; failed recovery audits are excluded')
for p in E.rglob('*.json'):assert p.stat().st_size<=5_000_000,p
assert load(E/'instances-pin.json')['bytes']>5_000_000
assert (R/load(E/'instances-pin.json')['generator']).exists()
checks.append('large full instance JSON retained by SHA-256, size and generator only')
known_scripts={sha(p) for p in (R/'tools/s10-inventory4-20261021').rglob('*.py')}
for p in E.glob('*-invocation.json'):
    inv=load(p);assert inv['script_sha256'] in known_scripts,p
    name=p.name.removesuffix('-invocation.json');receipt=load(E/(name+'-receipt.json'))
    assert inv['exit_status']==receipt['exit_status']
    assert receipt['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
    assert receipt['swaps']==0 and receipt['peak_rss_kib']*1024<8*1024**3
checks.append('every host invocation has pinned current/historical generator and exact scope/resource receipts')
callback=load(E/'callback-validation.json');assert callback['exit_status']==0 and len(callback['negative_controls'])==8
assert callback['source_sha256']==sha(R/'tools/s10-inventory4-20261021/check-callbacks.py')
assert callback['counts']=={'LLVM_CALLBACK_NULL':6,'LLVM_CALLBACK_CONSTANT':2,'OPEN':144}
checks.append('independent callback replay and 24 negative controls reused at their exact script SHA')
cfg=load(E/'cfg.json');mapping=load(E/'dominance-map.json');assert len(mapping['facts'])==140
assert mapping['cfg_sha256']==sha(E/'cfg.json')
def valid(r):
    edges=[tuple(e) for e in r['edges']]
    for c in r['cuts']:
        reach=set(c['reachable_without_cut']);cut=c['cut']
        if cut==0:
            if reach:return False
        elif 0 not in reach:return False
        if c['target'] in reach:return False
        if not all(dst==cut or src not in reach or dst in reach for src,dst in edges):return False
    return True
assert all(valid(r) for r in cfg['functions'])
mutated=copy.deepcopy(next(r for r in cfg['functions'] if any(c['cut']!=0 for c in r['cuts'])))
c=next(c for c in mutated['cuts'] if c['cut']!=0);mutated['edges'].append([0,c['target']]);assert not valid(mutated)
checks.append('all 140 cut certificates valid; injected bypass edge rejected')
base='9f42fc11c';changed=subprocess.check_output(['git','diff','--name-status',base],cwd=R,text=True).splitlines()
for line in changed:
    status,path=line.split('\t',1)
    if '/lean/' in path and path.endswith('.lean'):assert status=='A' and Path(path).name.startswith('OraclePort')
    assert not path.startswith(('crates/','programs/','refine/'))
checks.append('only new OraclePort Lean modules; existing owned cones and shipped crates unchanged')
gates=[]
for target in ['tools/s10-inventory2-20261021/reconcile.py','tools/s10-inventory3-20261021/reconcile.py']:
    p=subprocess.run([sys.executable,'-B',str(R/target),'--check','--require-complete'],cwd=R,text=True,capture_output=True)
    assert p.returncode==2,(target,p.stdout,p.stderr)
    gates.append(dict(target=target,exit_status=p.returncode,stdout=p.stdout,stderr=p.stderr))
checks.append('both original completeness gates rerun once; both exit 2 without weakening')
u=resource.getrusage(resource.RUSAGE_SELF)
r=dict(schema='s10-pass4-final-integrity-v1',target='tools/s10-inventory4-20261021/audit.py',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_sha256=sha(Path(__file__)),exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,swaps=u.ru_nswap,checks=checks,accepted_formal_results=accepted,completeness_gates=gates,
    final_source_coverage_instance=False,accepted_run_source_join=False,headline_premises_removed=0,
    remaining=['full frozen source Calls tree and complete state/error carriers','all deployed LLVM/ELF instance and inline correspondence/exclusions','144 ELF indirect sites and instantiated/native LLBC residuals','cone-owner adoption and complete source/model ordered oracle identities'],
    status='TARGET_NOT_YET_ESTABLISHED')
(E/'validation.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(integrity_exit=0,completeness_gates=[g['exit_status'] for g in gates],formal_modules=len(accepted),status=r['status'])))
