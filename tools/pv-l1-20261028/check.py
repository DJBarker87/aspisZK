"""Private-source env-J check using the unchanged host run2.py, with receipts."""
import pathlib,sys,subprocess,json,hashlib,shlex,time,re,datetime,atexit
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-l1-20261028'
H='/home/dombarker/project-offloads/codex-pv-l1-20261028'; P=H;host='dombarker@100.108.41.90'
A=int(sys.argv[1]);M=sys.argv[2];assert 51600<=A<=51699
# Enforce ruling (d) before consuming an ID; never depend on estimated wait time.
prior_refusals=[json.loads(p.read_text()) for p in E.glob('*refusal*.json')]
if prior_refusals:
 last=max(datetime.datetime.fromisoformat(r['utc']) for r in prior_refusals)
 remaining=180-(datetime.datetime.now(datetime.timezone.utc)-last).total_seconds()
 if remaining>0:
  print(f'WAIT: {remaining:.1f}s remain before another admission check; no ID consumed',flush=True)
  sys.exit(77)

def transport(cmd, **kw):
 must_check=kw.pop('check',False)
 for retry in range(11):
  r=subprocess.run(cmd, **kw)
  if r.returncode!=255:
   if must_check:r.check_returncode()
   return r
  with (E/'transport-retries.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=A,retry=retry,command=cmd,stderr=r.stderr))+'\n')
  if retry==10:raise RuntimeError('ten transient transport retries exhausted')
  print('transient SSH transport; retry in 60 seconds',flush=True);time.sleep(60)
 return r

rows=[json.loads(p.read_text()) for d in [E] for p in d.glob('receipt-[0-9]*.json')];charged=sum(r.get('exit') is not None for r in rows)
assert charged<100
# Ruling (p-prime): a vanished cgroup before launch keeps the same unlaunched ID.
prior_admission=json.loads((E/f'refusal-{A}.json').read_text()) if (E/f'refusal-{A}.json').exists() else {}
scan_race=bool(re.search(r'(?:FileNotFoundError|OSError): \[Errno (?:2|19)\]',prior_admission.get('error','')))
launched=any(json.loads(l).get('attempt')==A and not json.loads(l).get('confirmed_not_launched',False) for l in (E/'launches.jsonl').read_text().splitlines()) if (E/'launches.jsonl').exists() else False
assert not launched and not (E/f'receipt-{A}.json').exists(), 'compiler already launched under ID'
# Ruling m-prime: prelaunch metadata/refusals do not consume an ID.
if (E/f'refusal-{A}.json').exists():
 archive=E/f'admission-history-{A}-{time.time_ns()}.json'
 archive.write_bytes((E/f'refusal-{A}.json').read_bytes())
if scan_race:
 races=list(E.glob(f'barrier-race-{A}-*.json'))
 assert len(races)<=3,'fourth transient scan race: stop and report'
 with (E/'barrier-race-retries.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=A,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),ruling='p-prime',previous_admission=prior_admission,compiler_was_launched=False))+'\n')

# Read-only cross-job collision check before consuming each subsequent ID.
id_code = r"""import pathlib,re,json
root=pathlib.Path('/home/dombarker/project-offloads');hits=[]
pat=re.compile(r'(^|[-_])ATTEMPT([-_.]|$)')
for job in root.glob('codex-pv-*'):
 if job.name=='codex-pv-l1-20261028':continue
 for p in job.glob('evidence/**/*'):
  if len(p.relative_to(job).parts)<=5 and p.is_file() and pat.search(p.name):hits.append(str(p))
sent=root/'r1-privacy-build-integration-20261019/evidence/sent.txt'
lines=[l for l in sent.read_text().splitlines() if re.search(r'\bATTEMPT\b',l)]
print(json.dumps(dict(attempt=ATTEMPT,other_receipt_hits=hits,sent_hits=lines)))
""".replace('ATTEMPT',str(A))
id_result=transport(['ssh',host,'python3 -c '+shlex.quote(id_code)],capture_output=True,text=True)
assert id_result.returncode==0,id_result.stderr
id_audit=json.loads(id_result.stdout);(E/f'id-audit-{A}.json').write_text(json.dumps(id_audit,indent=2)+'\n')
assert not id_audit['other_receipt_hits'] and not id_audit['sent_hits'],id_audit
S=R/'docs/research/v8-r0-zk-20261009/lean'/(M+'.lean')
if len(sys.argv)>3:S=R/sys.argv[3]
assert S.is_file();sha=hashlib.sha256(S.read_bytes()).hexdigest()
if not (E/f'used-{A}.json').exists(): (E/f'used-{A}.json').write_text(json.dumps(dict(attempt=A,target=M,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))+'\n')

def ssh(c):return transport(['ssh',host,c],capture_output=True,text=True)
r=ssh(f'python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py {H}/evidence/pvl1-reservation-{A}.json > {H}/evidence/pvl1-reservation-{A}.log 2>&1\nreservation_status=$?\ncat {H}/evidence/pvl1-reservation-{A}.log\nexit $reservation_status')
(E/f'reservation-{A}.log').write_text(r.stdout+r.stderr)
admission=json.loads(r.stdout.strip().splitlines()[-1])
admission.setdefault('utc',datetime.datetime.now(datetime.timezone.utc).isoformat())
if r.returncode != 0 or not admission['allowed']:
 (E/f'refusal-{A}.json').write_text(json.dumps(admission,indent=2)+'\n')
 if re.search(r'(?:FileNotFoundError|OSError): \[Errno (?:2|19)\]',admission.get('error','')):
  index=len(list(E.glob(f'barrier-race-{A}-*.json')))
  (E/f'barrier-race-{A}-{index}.json').write_text(json.dumps(dict(attempt=A,admission=admission,classification='p-prime unlaunched scan race',retry_same_id=True,full_180_second_cooldown=True),indent=2)+'\n')
  (E/f'barrier-race-{A}-{index}.log').write_text(r.stdout+r.stderr)
  print('UNLAUNCHED SCAN RACE; same ID after cooldown',admission);sys.exit(79)
 print('REFUSED',admission);sys.exit(78)
transport(['scp','-q',f'{host}:{H}/evidence/pvl1-reservation-{A}.json',str(E/f'reservation-{A}.json')],check=True)
code=f'''import pathlib
p=pathlib.Path({P!r});(p/'sources'/pathlib.Path({M!r}).parent).mkdir(parents=True,exist_ok=True);(p/'objects'/pathlib.Path({M!r}).parent).mkdir(parents=True,exist_ok=True)
assert not (p/'objects'/({M!r}+'.olean')).exists(), 'never overwrite an accepted/reused object'
'''
r=ssh('python3 -c '+shlex.quote(code));assert r.returncode==0,r.stderr
transport(['scp','-q',str(S),f'{host}:{P}/sources/{M}.lean'],check=True)
code=f'''import pathlib,json,hashlib,re
e=json.load(open({P!r}+'/J.json'));roots=[pathlib.Path(x) for x in e['LEAN_PATH'].split(':')];d={{}}
for m in re.findall(r'^import\\s+(\\S+)',pathlib.Path({P!r}+'/sources/{M}.lean').read_text(),re.M):
 q=next((r/pathlib.Path(*m.split('.')).with_suffix('.olean') for r in roots if (r/pathlib.Path(*m.split('.')).with_suffix('.olean')).is_file()),None);d[m]=dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()) if q else None
print(json.dumps(d))
'''
r=ssh('python3 -c '+shlex.quote(code));assert r.returncode==0,r.stderr;deps=json.loads(r.stdout);fp=hashlib.sha256(json.dumps(dict(dependencies=deps,environment='h4 external objects and h6 source/object/transitive fingerprint verified private links'),sort_keys=True).encode()).hexdigest()
assert not any(r.get('source_sha256')==sha and r.get('deps_fingerprint')==fp and r.get('exit') is not None for r in rows),'unchanged input already compiled'
snapshot=f'{A}-{S.name}.txt';(E/snapshot).write_bytes(S.read_bytes());rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
cmd=['systemd-run','--user','--scope','--quiet','--unit=pvl1-lean-'+str(A),'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',H+f'/evidence/pvl1-time-{A}.log','timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',P+'/J.json',P+'/objects',P+'/sources',P+'/objects/'+M+'.olean',P+'/sources/'+M+'.lean','7000']
source_path=str(S.relative_to(R)); assert hashlib.sha256(subprocess.check_output(['git','show','HEAD:'+source_path])).hexdigest()==sha, 'commit exact source before launch'; blob=subprocess.check_output(['git','rev-parse',rev+':'+source_path],text=True).strip()
record=dict(attempt=A,target=M,source_revision=rev,source_path=source_path,source_git_blob=blob,source_sha256=sha,source_snapshot=snapshot,dependencies=deps,deps_fingerprint=fp,command=cmd,reservation=admission,shared_sources_written=False)
with (E/'launches.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
print('LAUNCH',A,M,flush=True);start=time.monotonic();r=subprocess.run(['ssh',host,shlex.join(cmd)+f' > {H}/evidence/pvl1-out-{A}.log 2>&1'],capture_output=True,text=True);record.update(launcher_exit=r.returncode,wall_seconds=time.monotonic()-start);(E/f'submission-{A}.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr,wall=record['wall_seconds']))+'\n')
if r.returncode==78:
 (E/f'refusal-{A}.json').write_text(json.dumps(dict(allowed=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),reason='scope launcher exit78 after initial admission; wait under lead rulings (d)/(e)/(m)'),indent=2)+'\n')
for name in ['out','time']:
 q=ssh(f'cat {H}/evidence/pvl1-{name}-{A}.log');(E/f'{name}-{A}.log').write_text(q.stdout+q.stderr)
 if q.returncode != 0: raise RuntimeError('Receipt fetch failed; recover original log read-only before accepting or scheduling another compile: '+name)
out=(E/f'out-{A}.log').read_text();tim=(E/f'time-{A}.log').read_text();print(out[-8500:],flush=True)
m=re.search(r'Exit status: (\d+)',tim);record['exit']=int(m[1]) if m else None
m=re.search(r'Maximum resident set size \(kbytes\): (\d+)',tim);record['peak_rss_bytes']=int(m[1])*1024 if m else None
m=re.search(r'Swaps: (\d+)',tim);record['swaps']=int(m[1]) if m else None
elapsed=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)',tim)
if elapsed:
 host_wall=0
 for component in elapsed[1].split(':'):host_wall=host_wall*60+float(component)
 record['host_wall_seconds']=host_wall
record['wall_seconds_note']='wall_seconds is submission/transport elapsed; host_wall_seconds is GNU time elapsed for the capped command'
record['axioms']=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",out)
record['accepted']=r.returncode==0 and record['exit']==0 and 'error:' not in out and 'sorryAx' not in out
(E/f'receipt-{A}.json').write_text(json.dumps(record,indent=2)+'\n');print('RECEIPT',json.dumps({k:record.get(k) for k in ['attempt','exit','wall_seconds','peak_rss_bytes','swaps','accepted']}),flush=True)
sys.exit(0 if record['accepted'] else 1)
