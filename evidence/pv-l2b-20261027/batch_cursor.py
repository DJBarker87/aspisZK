#!/usr/bin/env python3
"""One finite sequence of focused source-trace proofs in one reserved 8 GiB scope.

Uses the unchanged env-J executor. Every compile has its own time/axioms/ID
receipt. No shared launcher, source, object, or reservation code is changed.
"""
import datetime,hashlib,json,pathlib,re,shlex,subprocess,sys,time
E=pathlib.Path(__file__).resolve().parent;ROOT=E.parent.parent
JOB='/home/dombarker/project-offloads/codex-pv-l2b-20261027';HOST='dombarker@100.108.41.90'
T='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
RES='/home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py'
def ssh(cmd):return subprocess.run(['ssh',HOST,cmd],text=True,capture_output=True)
startid=int(sys.argv[1]);module=sys.argv[2] if len(sys.argv)>2 else 'PV_L2B_Cursor';f=ROOT/'docs/research/v8-r0-zk-20261009/lean'/f'{module}.lean'
for p in list((E/'receipts').glob('*/reservation.json'))+list((E/'kani').glob('*/reservation.json'))+list(E.glob('batch-*/reservation.json')):
 try:
  x=json.loads(p.read_text())
  if x.get('allowed') is not False:continue
  t=x.get('utc');stamp=float(t) if isinstance(t,(int,float)) else datetime.datetime.fromisoformat(t).timestamp()
  if time.time()-stamp<(30 if 'error' in x else 180):print('mandatory wait',p);sys.exit(78)
 except (ValueError,TypeError):pass
gate=E/f'batch-{startid}';gate.mkdir(exist_ok=False)
r=ssh(f'python3 {RES} {JOB}/reservation-batch-{startid}.json > {JOB}/reservation-batch-{startid}.log 2>&1; cat {JOB}/reservation-batch-{startid}.log')
(gate/'preflight.log').write_text(r.stdout+r.stderr)
x=ssh(f'cat {JOB}/reservation-batch-{startid}.json');(gate/'reservation.json').write_text(x.stdout)
if not json.loads(x.stdout)['allowed']:print('RESERVATION HOLD');sys.exit(78)
s=json.loads((E/'progress.json').read_text());q=json.loads((E/'proof-queue.json').read_text())
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
idx=s['index']
if f.exists():
 text=f.read_text()
else:
 item=q[idx];assert item['module']==module and 'initial' in item
 end='end '+item['namespace'];text=item['initial'].rstrip()[:-len(end)]+item['body']+'\n'+''.join('#print axioms '+n+'\n' for n in item['theorems'])+end+'\n';idx+=1
specs=[]
if len(sys.argv)>3 and sys.argv[3]=='with-source-words':
 extra=ROOT/'docs/research/v8-r0-zk-20261009/lean/PV_L2B_SourceWords.lean'
 specs.append(dict(attempt=startid,module='PV_L2B_SourceWords',source=extra.read_text(),q_after=s['index']))
specs.append(dict(attempt=startid+len(specs),module=module,source=text,q_after=idx))
while idx<len(q) and q[idx]['module']==module:
 item=q[idx];end='end '+item['namespace']
 text=text.rstrip()[:-len(end)]+item['body']+'\n'+''.join('#print axioms '+n+'\n' for n in item['theorems'])+end+'\n'
 specs.append(dict(attempt=startid+len(specs),module=module,source=text,q_after=idx+1));idx+=1
assert all(53000<=v['attempt']<53297 for v in specs)
(gate/'manifest.json').write_text(json.dumps(specs)+'\n')
subprocess.run(['scp','-q',str(gate/'manifest.json'),f'{HOST}:{JOB}/cursor-manifest.json'],check=True)
code='''import json,pathlib,subprocess,sys,hashlib,re
job=pathlib.Path(sys.argv[1]);T=sys.argv[2];items=json.load(open(job/'cursor-manifest.json'))
env='/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'
for x in items:
 a=x['attempt'];m=x['module'];src=job/(m+'.lean');src.write_text(x['source'])
 paths=[str(job)]+json.load(open(env))['LEAN_PATH'].split(':');deps=[]
 for name in re.findall(r'^import (\\S+)',x['source'],re.M):
  p=next((pathlib.Path(r)/(name.replace('.','/')+'.olean') for r in paths if (pathlib.Path(r)/(name.replace('.','/')+'.olean')).is_file()),None)
  deps.append(dict(module=name,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest() if p else None))
 (job/f'deps-{a}.json').write_text(json.dumps(deps,sort_keys=True)+'\\n')
 with (job/f'out-{a}.log').open('w') as out:
  p=subprocess.run(['/usr/bin/time','-v','-o',str(job/f'time-{a}.log'),'timeout','900','python3',T+'/run2.py',env,str(job),str(job),str(job/(m+'.olean')),str(src),'7000'],stdout=out,stderr=subprocess.STDOUT)
  out.write(f'\\nexit={p.returncode}\\n')
 print(a,p.returncode,flush=True)
 if p.returncode:break
'''
cmd=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3','-u','-c',code,JOB,T]
(gate/'command.json').write_text(json.dumps(cmd,indent=2)+'\n')
r=ssh(shlex.join(cmd));(gate/'scope.log').write_text(r.stdout+r.stderr);print(r.stdout+r.stderr)
done=[int(a) for a in re.findall(r'^(\d+) \d+$',r.stdout,re.M)]
assert done
for x in specs:
 a=x['attempt']
 if a not in done:continue
 d=E/'receipts'/str(a);d.mkdir(exist_ok=False);(d/'source.lean').write_text(x['source'])
 for name,remote in [('out.log',f'out-{a}.log'),('time.log',f'time-{a}.log'),('dependencies.json',f'deps-{a}.json')]:
  rr=ssh(f'cat {JOB}/{remote}');(d/name).write_text(rr.stdout+rr.stderr)
 (d/'reservation.json').write_bytes((gate/'reservation.json').read_bytes())
 out=(d/'out.log').read_text();tm=(d/'time.log').read_text()
 target_file=ROOT/'docs/research/v8-r0-zk-20261009/lean'/(x['module']+'.lean')
 rec=dict(attempt=a,module=x['module'],target=x['module'],revision=rev,source=str(target_file.relative_to(ROOT)),sha256=hashlib.sha256(x['source'].encode()).hexdigest(),
  exit=int(re.search(r'^exit=(\d+)',out,re.M)[1]),deps_fingerprint=hashlib.sha256((d/'dependencies.json').read_bytes()).hexdigest(),
  axioms=re.findall(r"'[^\n]+(?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",out),
  caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,lean_M=7000,TasksMax=64),scope='single sequential '+module+' stage; admission '+str(startid))
 for k,pat in [('wall',r'Elapsed \(wall clock\) time.*: (.+)'),('peak_RSS_KiB',r'Maximum resident set size \(kbytes\): (\d+)'),('swap',r'Swaps: (\d+)')]:rec[k]=re.search(pat,tm)[1]
 (d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
 with (E/'attempts.jsonl').open('a') as out:out.write(json.dumps(rec)+'\n')
 target_file.write_text(x['source']);s.update(index=x['q_after'],next_id=specs[-1]['attempt']+1)
 (E/'progress.json').write_text(json.dumps(s,indent=2)+'\n')
 print(a,rec['exit'],rec['wall'])
 if rec['exit']:print(out if isinstance(out,str) else (d/'out.log').read_text());sys.exit(1)
