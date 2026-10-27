from pathlib import Path
import subprocess,json,hashlib,sys,re,shlex
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-canon-20261027'; B='/home/dombarker/project-offloads'; D=B+'/codex-pv-canon-20261027'; H='dombarker@100.108.41.90'
m=sys.argv[1]; p=R/'docs/research/v8-r0-zk-20261009/lean'/ (m+'.lean'); assert p.name.startswith('PV_Canon_')
tp=E/'tally.json'; t=json.loads(tp.read_text()) if tp.exists() else dict(lean=0,kani=0,next_id=44200,attempts=[])
assert t['lean']<100; n=t['next_id']; assert n<=44499
t['next_id']+=1; t['attempts'].append(dict(id=n,module=m));tp.write_text(json.dumps(t,indent=2)+'\n')
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
# A private overlay consumes env-J read-only. Existing reservation/barrier/run2 are reused.
code='''from pathlib import Path
import subprocess,json,os,hashlib,time,re
B=Path('/home/dombarker/project-offloads');D=B/'codex-pv-canon-20261027';N=ATTEMPT;M=MODULE
O=D/'receipts'/str(N);O.mkdir(parents=True,exist_ok=False)
G=B/'codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
a=subprocess.run(['python3',str(G/'reservation.py'),str(O/'reservation.json')],stdout=open(O/'reservation.log','w'),stderr=subprocess.STDOUT)
if a.returncode: print((O/'reservation.log').read_text());raise SystemExit(a.returncode)
e=json.loads((B/'r1-privacy-build-integration-20261019/env/J.json').read_text()); 
for root in e['LEAN_PATH'].split(':'):
 for source in Path(root).rglob('*.olean*'):
  if source.is_file():
   dest=D/'objects'/source.relative_to(Path(root));dest.parent.mkdir(parents=True,exist_ok=True)
   if not dest.exists() and not dest.is_symlink(): dest.symlink_to(source)
e['LEAN_PATH']=str(D/'objects')+':'+e['LEAN_PATH'];(D/'env.json').write_text(json.dumps(e))
src=D/'sources'/(M+'.lean');obj=D/'objects'/(M+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
meta=dict(target=M,attempt=N,revision=REVISION,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),env='J read-only with private overlay')
deps={}
for module in re.findall(r'^import (\S+)',src.read_text(),re.M):
 for root in e['LEAN_PATH'].split(':'):
  dep=Path(root)/(module.replace('.','/')+'.olean')
  if dep.is_file(): deps[module]=dict(path=str(dep.resolve()),sha256=hashlib.sha256(dep.read_bytes()).hexdigest());break
meta['dependencies']=deps
start=time.monotonic()
c=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(G/'barrier.py'),str(O/'barrier.json'),'/usr/bin/time','-v','-o',str(O/'time.log'),'timeout','900','python3',str(B/'aspis-fs-generic-20261006/evidence/run2.py'),str(D/'env.json'),str(D/'objects'),str(D/'sources'),str(obj),str(src),'7000']
a=subprocess.run(c,stdout=open(O/'out.log','w'),stderr=subprocess.STDOUT)
meta.update(exit=a.returncode,wall_seconds=time.monotonic()-start,time_log=(O/'time.log').read_text() if (O/'time.log').exists() else None,axioms=[l for l in (O/'out.log').read_text().splitlines() if 'axioms' in l]);(O/'receipt.json').write_text(json.dumps(meta,indent=2));print((O/'out.log').read_text());print(json.dumps(meta))
'''.replace('ATTEMPT',str(n)).replace('MODULE',repr(m)).replace('REVISION',repr(rev))
subprocess.run(['ssh',H,'mkdir -p '+D+'/sources/'+str(Path(m).parent)],check=True)
subprocess.run(['scp',str(p),H+':'+D+'/sources/'+m+'.lean'],check=True,stdout=subprocess.DEVNULL)
a=subprocess.run(['ssh',H,'python3 -'],input=code,text=True,capture_output=True);print(a.stdout+a.stderr)
(E/f'{n}-launcher.log').write_text(a.stdout+a.stderr)
subprocess.run(['scp','-r',H+':'+D+'/receipts/'+str(n),str(E)],stdout=subprocess.DEVNULL)
rp=E/str(n)/'receipt.json'
if rp.exists() and json.loads(rp.read_text())['time_log'] is not None:
 t=json.loads(tp.read_text());t['lean']+=1;t['attempts'][-1]['charged']=True;tp.write_text(json.dumps(t,indent=2)+'\n')
else: print('UNCHARGED reservation refusal: cooldown 180s; next unused ID')
