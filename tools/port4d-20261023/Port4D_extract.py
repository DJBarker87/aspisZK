from pathlib import Path
import json,subprocess,sys,shlex,hashlib
R=Path(__file__).resolve().parents[2];T=R/'tools/port4d-20261023';E=R/'evidence/port4d-20261023'
H='dombarker@100.108.41.90'; B='/home/dombarker/project-offloads/codex-cx-port4d-20261023'; oldB='/home/dombarker/project-offloads/codex-cx-ports3-20261023'
kind=sys.argv[1]; scope=sys.argv[2] if len(sys.argv)>2 else 'round'; n=1+max((int(p.stem.split('-')[1]) for p in T.glob(kind+'-*.json')),default=0); a=f'{kind}-{n:03d}'
old=json.loads((R/('tools/ports3-20261023/charon-005.json' if kind=='charon' else 'tools/ports3-20261023/aeneas-004.json')).read_text())
c=old['command'];c=[s.replace(oldB,B).replace('Port3_StageChildren','Port4D_Children') for s in c]
if kind=='charon':
 # Keep layout selection; replace all requested body selections with the local round.
 i=c.index('--include'); j=c.index('--consts'); keep=[]
 for n in range(i,j):
  if c[n]=='--include' and not ('crate::verifier::candidate::' in c[n+1] or c[n+1] in ['crate::verifier::resume','crate::verifier::finish_relation','crate::verifier::accumulate_batched_with_node'] or '{' in c[n+1] or 'crate::verifier::_::' in c[n+1]): keep+=c[n:n+2]
 roots=['--include','crate::verifier::finish_relation_round','--start-from','crate::verifier::finish_relation_round'] if scope=='round' else ['--include','crate::verifier::candidate::tx1','--start-from','crate::verifier::candidate::tx1','--include','crate::verifier::_::finish','--include','crate::verifier::_::value']
 c=c[:i]+roots+keep+c[j:]
 old['env']['CARGO_TARGET_DIR']=B+'/charon-target'
 if not (E/'charon-001/receipt.json').exists(): subprocess.run(['ssh',H,f'mkdir -p {B}; cp -a {oldB}/src {B}/src'],check=True)
else:
 old['sources']=['Port4D_Children.llbc']
old.update(attempt=a,command=c,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),expected_time='Optimized focused round MIR extraction' if kind=='charon' else 'Focused symbolic Aeneas round translation',deps_fingerprint={'scope':'Read-only inherited pinned source snapshot; complete current round; backend children opaque'})
cfg=T/(a+'.json');cfg.write_text(json.dumps(old,indent=2)+'\n')
admission=(T/'Port4D_compile.py').read_text().split("admission='''",1)[1].split("'''",1)[0]
r=subprocess.run(['ssh',H,'python3 -c '+shlex.quote(admission)],capture_output=True,text=True,check=True);(E/(a+'-reservation.json')).write_text(r.stdout)
subprocess.run(['scp','-q',str(cfg),str(T/'Port4D_run_host.py'),H+':'+B+'/'],check=True)
r=subprocess.run(['ssh',H,f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 Port4D_run_host.py {a}.json'],capture_output=True,text=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
subprocess.run(['scp','-qr',H+':'+B+'/'+a,str(E)],check=True)
print(r.stdout);print(r.stderr);sys.exit(r.returncode)
