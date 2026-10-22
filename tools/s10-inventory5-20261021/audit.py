#!/usr/bin/env python3
"""Focused receipt/source audit; the completeness gates keep their criteria.
Run --gates once on a new packet. Subsequent integrity checks reuse that receipt.
"""
import argparse,hashlib,json,re,resource,subprocess,sys,time
from pathlib import Path
start=time.monotonic();R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s10-inventory5-20261021';T=R/'tools/s10-inventory5-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
a=argparse.ArgumentParser();a.add_argument('--gates',action='store_true');args=a.parse_args()
checks=[]
for script in ['generate-order.py','stage-order.py','boundaries.py','check-callbacks.py']:
    p=subprocess.run([sys.executable,'-B',str(T/script),'--check'],cwd=R,text=True,capture_output=True)
    checks.append(dict(target=script,exit_status=p.returncode,stdout=p.stdout,stderr=p.stderr));assert p.returncode==0,checks[-1]
formal=load(E/'manifest.json');latest={}
for result in formal['attempts']:
    module=result['module'];d=E/(module+'-'+str(result['attempt']));cmd=load(d/'command.json');log=(d/'lean.log').read_text()
    assert sha(d/'source.lean.txt')==result['source_sha256']
    assert result['source_revision']==cmd['source_revision']
    assert result['exit_status']==0 or module=='OraclePortS10StrictOrder'
    if result['exit_status']:continue
    assert result['peak_rss_bytes']<4_400_000_000 and result['swaps']==0
    for dep in result['dependencies']:assert sha(Path(dep['path']))==dep['sha256'],dep
    assert all(line in log for line in result['print_axioms'])
    assert result['print_axioms']
    for line in result['print_axioms']:
        if 'depends on axioms:' in line:
            allowed=set(re.search(r'\[([^\]]*)\]',line)[1].split(', '))
            assert allowed<={'propext','Classical.choice','Quot.sound'},line
    latest[module]=result
assert len(latest)==9
for module,result in latest.items():
    source=B/'lean'/(module+'.lean');assert sha(source)==result['source_sha256']
    text=source.read_text();assert not re.search(r'\b(sorry|admit|native_decide|maxHeartbeats|maxRecDepth)\b',text)
    ns=re.search(r'^namespace (\S+)',text,re.M)
    names=re.findall(r'^theorem (\w+)',text,re.M)
    for name in names:assert any("'"+ns[1]+'.'+name+"'" in line for line in result['print_axioms']),(module,name)
base=load(E/'indirect-host-invocation.json')['source_revision']
diff=subprocess.check_output(['git','diff','--name-status',base,'--','crates','programs',str(B/'lean'),str(B/'lean-candidates')],cwd=R,text=True)
for line in diff.splitlines():
    status,name=line.split('\t',1)
    assert status=='A' and name.startswith(str(B.relative_to(R))+'/lean/OraclePortS10'),line
callback=load(E/'callback-validation.json');assert callback['counts']=={'LLVM_CALLBACK_CONSTANT':15,'LLVM_CALLBACK_NULL':6,'OPEN':131}
assert len(callback['negative_controls'])*3+len(callback['field_negative_controls'])==189
for r in [load(E/'indirect-host-v2-receipt.json'),load(E/'resolve-host-v2-receipt.json')]+[load(E/f'build-default-v{v}-receipt-receipt.json') for v in ['1','2']]:
    assert r['exit_status']==0 and r['swaps']==0
    assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for tag,source in [('indirect-host-v2','indirect-host.py'),('resolve-host-v2','resolve-host.py')]:
    assert load(E/(tag+'-invocation.json'))['script_sha256']==sha(T/source)
for v,wrapper in [('1',T/'historical/rustc-debug-full.py'),('2',T/'rustc-debug.py')]:
    assert load(E/f'build-default-v{v}-command.json')['wrapper_sha256']==sha(wrapper)
comparison=load(E/'debug-comparisons.json')['results'];assert len(comparison)==2
for r in comparison:
    assert not r['allocated_sections_and_relocations_identical']
    assert not next(s['equal'] for s in r['sections'] if s['section']=='.text')
    assert 'dwarf' not in r
files=[*T.rglob('*.py'),*[B/'lean'/(m+'.lean') for m in latest]]
pins={str(p.relative_to(R)):sha(p) for p in sorted(files)}
(E/'frozen-sources.json').write_text(json.dumps(pins,indent=2,sort_keys=True)+'\n')
gate_commands=[['python3','-B','tools/s10-inventory2-20261021/reconcile.py','--check','--require-complete'],['python3','-B','tools/s10-inventory3-20261021/reconcile.py','--check','--require-complete']]
if args.gates:
    assert not (E/'gates.json').exists(),'unchanged full gates already recorded'
    gates=[]
    for command in gate_commands:
        before=time.monotonic();p=subprocess.run(command,cwd=R,text=True,capture_output=True);u=resource.getrusage(resource.RUSAGE_CHILDREN)
        gates.append(dict(command=command,script_sha256=sha(R/command[2]),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),exit_status=p.returncode,wall_seconds=time.monotonic()-before,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,swaps=u.ru_nswap,stdout=p.stdout,stderr=p.stderr,print_axioms='N/A: completeness check only; formal axioms recorded separately'))
    (E/'gates.json').write_text(json.dumps(gates,indent=2,sort_keys=True)+'\n')
else:gates=load(E/'gates.json')
for g in gates:
    assert g['exit_status']==2 and 'INCOMPLETE' in g['stdout'],g
    assert sha(R/g['command'][2])==g['script_sha256']
for p in E.rglob('*.json'):assert p.stat().st_size<=5_000_000,p
u=resource.getrusage(resource.RUSAGE_SELF)
receipt=dict(schema='s10-pass5-validation-v1',target='tools/s10-inventory5-20261021/audit.py',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_sha256=sha(Path(__file__)),exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,swaps=u.ru_nswap,checks=checks,formal_results=list(latest.values()),gate_exit_statuses=[g['exit_status'] for g in gates],print_axioms='Complete standard-axiom lines in formal_results; no new trusted axiom.',release_target='NOT_ESTABLISHED: complete frozen source tree/carriers, caller identities, final inline-instance correspondence and boundary/owner adoption remain open.')
(E/'validation.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(integrity_exit_status=0,formal_successes=len(latest),gate_exit_statuses=receipt['gate_exit_statuses'],release_target='NOT_ESTABLISHED')))
