"""Private-source env-J check using the unchanged host run2.py, with receipts."""
import pathlib,sys,subprocess,json,hashlib,shlex,time,re,datetime,atexit
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume7'
H='/home/dombarker/project-offloads/codex-pv-reach-20261027'; P=H+'/lean';host='dombarker@100.108.41.90'
A=int(sys.argv[1]);M=sys.argv[2];assert 39400<=A<=39499 and ('PV_RE_' in M or M in [x['module'].replace('.','/') for x in json.loads((E/'project-closure.json').read_text())])
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/pv-reach-20261027'
assert str(R)=='/Users/dominic/ZK/.worktrees/pv-reach'
assert json.loads((E/'h4-verification.json').read_text())['mismatches']==[]
rows=[json.loads(p.read_text()) for folder in [E] for p in folder.glob('receipt-[0-9]*.json')];charged=sum(r.get('exit') is not None for r in rows)
assert charged<100 and (A<39497 or 'Audit' in M)
assert not (E/f'used-{A}.json').exists()
S=R/'docs/research/v8-r0-zk-20261009/lean'/(M+'.lean')
if len(sys.argv)>3:S=R/sys.argv[3]
assert S.is_file();sha=hashlib.sha256(S.read_bytes()).hexdigest()
(E/f'used-{A}.json').write_text(json.dumps(dict(attempt=A,target=M,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))+'\n')

def ssh(c,submitted=False):
 r=subprocess.run(['ssh',host,c],capture_output=True,text=True)
 if r.returncode!=255 or submitted:return r
 for retry in range(1,11):
  with (E/'transport-retries.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=A,retry=retry,command=c,stderr=r.stderr))+'\n')
  time.sleep(60)
  r=subprocess.run(['ssh',host,c],capture_output=True,text=True)
  if r.returncode!=255:return r
 return r

def scp(args):
 for retry in range(11):
  r=subprocess.run(['scp','-q']+args,capture_output=True,text=True)
  if r.returncode!=255:r.check_returncode();return
  with (E/'transport-retries.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=A,retry=retry,scp=args,stderr=r.stderr))+'\n')
  if retry<10:time.sleep(60)
 r.check_returncode()
r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2x-20261023/S2X_reservation.py {H}/evidence/pvre-reservation-{A}.json > {H}/evidence/pvre-reservation-{A}.log 2>&1; admission_status=$?; cat {H}/evidence/pvre-reservation-{A}.log; exit $admission_status')
(E/f'reservation-{A}.log').write_text(r.stdout+r.stderr)
assert r.returncode in [0,78],r.stderr+r.stdout
admission=json.loads(r.stdout.strip().splitlines()[-1])
if r.returncode != 0 or not admission['allowed']:
 (E/f'refusal-{A}.json').write_text(json.dumps(admission,indent=2)+'\n');print('REFUSED',admission);sys.exit(78)
scp([f'{host}:{H}/evidence/pvre-reservation-{A}.json',str(E/f'reservation-{A}.json')])
code=f'''import pathlib,json,hashlib,re
p=pathlib.Path({P!r});(p/'sources'/pathlib.Path({M!r}).parent).mkdir(parents=True,exist_ok=True);(p/'objects'/pathlib.Path({M!r}).parent).mkdir(parents=True,exist_ok=True)
e=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'));e['LEAN_PATH']=str(p/'objects');(p/'J.json').write_text(json.dumps(e))
'''
r=ssh('python3 -c '+shlex.quote(code));assert r.returncode==0,r.stderr
scp([str(S),f'{host}:{P}/sources/{M}.lean'])
authority_map={x['module']:x for x in json.loads((E/'project-closure.json').read_text())}
source_closure=set()
def add_source_dependencies(name):
 if name in source_closure:return
 source_closure.add(name)
 if name in authority_map:
  for dep in authority_map[name]['imports']:add_source_dependencies(dep)
add_source_dependencies(M.replace('/','.'))
source_closure.discard(M.replace('/','.'))
code=f'''import pathlib,json,hashlib,re
e=json.load(open({P!r}+'/J.json'));roots=[pathlib.Path(x) for x in e['LEAN_PATH'].split(':')];d={{}}
for m in {sorted(source_closure)!r}+['Aeneas','Aeneas.Command','AeneasMeta.Extensions','Init.Prelude','Mathlib.Data.List.GetD']+re.findall(r'^import\\s+(\\S+)',pathlib.Path({P!r}+'/sources/{M}.lean').read_text(),re.M):
 q=next((r/pathlib.Path(*m.split('.')).with_suffix('.olean') for r in roots if (r/pathlib.Path(*m.split('.')).with_suffix('.olean')).is_file()),None);d[m]=dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()) if q else None
print(json.dumps(d))
'''
r=ssh('python3 -c '+shlex.quote(code));assert r.returncode==0,r.stderr;deps=json.loads(r.stdout);deps['private_cache_environment']={'companion_restoration':'resume4/cache-links.json','authority':'resume7/project-closure.json','pinned_links_sha256':hashlib.sha256((E/'pinned-cache-links.json').read_bytes()).hexdigest() if (E/'pinned-cache-links.json').exists() else None};fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest()
assert not any(r.get('source_sha256')==sha and r.get('deps_fingerprint')==fp and r.get('exit') is not None for r in rows),'unchanged input already compiled'
snapshot=f'{A}-{S.name}.txt';(E/snapshot).write_bytes(S.read_bytes());rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
cmd=['systemd-run','--user','--scope','--quiet','--unit=pvre-lean-'+str(A),'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',H+f'/evidence/pvre-time-{A}.log','timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',P+'/J.json',P+'/objects',P+'/sources',P+'/objects/'+M+'.olean',P+'/sources/'+M+'.lean','7000']
authority_row=next((x for x in json.loads((E/'project-closure.json').read_text()) if x['module']==M.replace('/','.')),None)
if authority_row is None:
 current=subprocess.run(['git','rev-parse',rev+':'+str(S.relative_to(R))],capture_output=True,text=True)
 if current.returncode==0 and subprocess.check_output(['git','show',current.stdout.strip()])==S.read_bytes():
  authority_row=dict(module=M.replace('/','.'),authority='h5-own-branch',path=str(S.relative_to(R)),revision=rev,blob=current.stdout.strip(),sha256=sha)
record=dict(attempt=A,target=M,project_source_authority=authority_row,source_revision=rev,source_differs_from_revision=(subprocess.run(['git','show',rev+':'+str(S.relative_to(R))],capture_output=True).stdout != S.read_bytes()),source_sha256=sha,source_snapshot=snapshot,dependencies=deps,deps_fingerprint=fp,command=cmd,reservation=admission,shared_sources_written=False)
with (E/'launches.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
print('LAUNCH',A,M,flush=True);start=time.monotonic();r=ssh(shlex.join(cmd)+f' > {H}/evidence/pvre-out-{A}.log 2>&1',submitted=True);record.update(launcher_exit=r.returncode,wall_seconds=time.monotonic()-start)
for name in ['out','time']:
 q=ssh(f'cat {H}/evidence/pvre-{name}-{A}.log');(E/f'{name}-{A}.log').write_text(q.stdout+q.stderr)
out=(E/f'out-{A}.log').read_text();tim=(E/f'time-{A}.log').read_text();print(out[-8500:],flush=True)
m=re.search(r'Exit status: (\d+)',tim);record['exit']=int(m[1]) if m else None
m=re.search(r'Maximum resident set size \(kbytes\): (\d+)',tim);record['peak_rss_bytes']=int(m[1])*1024 if m else None
m=re.search(r'Swaps: (\d+)',tim);record['swaps']=int(m[1]) if m else None
record['axioms']=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",out)
record['accepted']=r.returncode==0 and record['exit']==0 and not re.search(r'(?m)^(?:.*:[0-9]+:[0-9]+: )?error:',out) and 'sorryAx' not in out
(E/f'receipt-{A}.json').write_text(json.dumps(record,indent=2)+'\n');print('RECEIPT',json.dumps({k:record.get(k) for k in ['attempt','exit','wall_seconds','peak_rss_bytes','swaps','accepted']}),flush=True)
sys.exit(0 if record['accepted'] else 1)
