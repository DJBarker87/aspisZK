"""Private-source env-J check using the unchanged host run2.py, with receipts."""
import pathlib,sys,subprocess,json,hashlib,shlex,time,re,datetime,atexit
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin16-20261027'
H='/home/dombarker/project-offloads/codex-pv-runjoin-20261026'; P=H+'/runjoin16-lean';host='dombarker@100.108.41.90'
A=int(sys.argv[1]);M=sys.argv[2];assert 50600<=A<=50899 and 'PV_RunJoin_' in M
assert (A>=50897) == ('TrustAudit16' in M), 'IDs 50897–50899 reserved for focused audit'
rows=[json.loads(p.read_text()) for p in E.glob('receipt-[0-9]*.json')];charged=sum(r.get('exit') is not None for r in rows)
assert charged<100 and (charged<97 or 'TrustAudit16' in M)
assert not (E/f'used-{A}.json').exists()
S=R/'docs/research/v8-r0-zk-20261009/lean'/(M+'.lean')
if len(sys.argv)>3:S=R/sys.argv[3]
assert S.is_file();sha=hashlib.sha256(S.read_bytes()).hexdigest()
(E/f'used-{A}.json').write_text(json.dumps(dict(attempt=A,target=M,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))+'\n')
atexit.register(lambda:subprocess.run([sys.executable,str(R/'tools/pv-runjoin16-20261027/tally.py')],stdout=subprocess.DEVNULL))
def ssh(c):return subprocess.run(['ssh',host,c],capture_output=True,text=True)
r=ssh(f'python3 {H}/reservation-existing.py {H}/evidence/pv16-reservation-{A}.json > {H}/evidence/pv16-reservation-{A}.log 2>&1\nreservation_status=$?\ncat {H}/evidence/pv16-reservation-{A}.log\nexit $reservation_status')
(E/f'reservation-{A}.log').write_text(r.stdout+r.stderr)
admission=json.loads(r.stdout.strip().splitlines()[-1])
if r.returncode != 0 or not admission['allowed']:
 (E/f'refusal-{A}.json').write_text(json.dumps(admission,indent=2)+'\n');print('REFUSED',admission);sys.exit(78)
subprocess.run(['scp','-q',f'{host}:{H}/evidence/pv16-reservation-{A}.json',str(E/f'reservation-{A}.json')],check=True)
code=f'''import pathlib,json,hashlib,re
p=pathlib.Path({P!r});(p/'sources'/pathlib.Path({M!r}).parent).mkdir(parents=True,exist_ok=True);(p/'objects'/pathlib.Path({M!r}).parent).mkdir(parents=True,exist_ok=True)
e=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'));e['LEAN_PATH']=str(p/'objects')+':{P}/std-cache:{H}/lean-objects:'+e['LEAN_PATH'];(p/'J.json').write_text(json.dumps(e))
'''
r=ssh('python3 -c '+shlex.quote(code));assert r.returncode==0,r.stderr
subprocess.run(['scp','-q',str(S),f'{host}:{P}/sources/{M}.lean'],check=True)
code=f'''import pathlib,json,hashlib,re
e=json.load(open({P!r}+'/J.json'));roots=[pathlib.Path(x) for x in e['LEAN_PATH'].split(':')];d={{}}
for m in re.findall(r'^import\\s+(\\S+)',pathlib.Path({P!r}+'/sources/{M}.lean').read_text(),re.M):
 q=next((r/pathlib.Path(*m.split('.')).with_suffix('.olean') for r in roots if (r/pathlib.Path(*m.split('.')).with_suffix('.olean')).is_file()),None);d[m]=dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()) if q else None
print(json.dumps(d))
'''
r=ssh('python3 -c '+shlex.quote(code));assert r.returncode==0,r.stderr;deps=json.loads(r.stdout);fp=hashlib.sha256(json.dumps(dict(dependencies=deps,private_standard_cache=P+'/std-cache',environment='restored standard-cache view v1'),sort_keys=True).encode()).hexdigest()
assert not any(r.get('source_sha256')==sha and r.get('deps_fingerprint')==fp and r.get('exit') is not None for r in rows),'unchanged input already compiled'
snapshot=f'{A}-{S.name}.txt';(E/snapshot).write_bytes(S.read_bytes());rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
cmd=['systemd-run','--user','--scope','--quiet','--unit=pv16-lean-'+str(A),'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',H+f'/evidence/pv16-time-{A}.log','timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',P+'/J.json',P+'/objects',P+'/sources',P+'/objects/'+M+'.olean',P+'/sources/'+M+'.lean','7000']
record=dict(attempt=A,target=M,source_revision=rev,source_sha256=sha,source_snapshot=snapshot,dependencies=deps,deps_fingerprint=fp,command=cmd,reservation=admission,shared_sources_written=False)
with (E/'launches.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
print('LAUNCH',A,M,flush=True);start=time.monotonic();r=ssh(shlex.join(cmd)+f' > {H}/evidence/pv16-out-{A}.log 2>&1');record.update(launcher_exit=r.returncode,wall_seconds=time.monotonic()-start)
for name in ['out','time']:
 q=ssh(f'cat {H}/evidence/pv16-{name}-{A}.log');(E/f'{name}-{A}.log').write_text(q.stdout+q.stderr)
out=(E/f'out-{A}.log').read_text();tim=(E/f'time-{A}.log').read_text();print(out[-8500:],flush=True)
m=re.search(r'Exit status: (\d+)',tim);record['exit']=int(m[1]) if m else None
m=re.search(r'Maximum resident set size \(kbytes\): (\d+)',tim);record['peak_rss_bytes']=int(m[1])*1024 if m else None
m=re.search(r'Swaps: (\d+)',tim);record['swaps']=int(m[1]) if m else None
record['axioms']=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",out)
record['accepted']=r.returncode==0 and record['exit']==0 and 'error:' not in out and 'sorryAx' not in out
(E/f'receipt-{A}.json').write_text(json.dumps(record,indent=2)+'\n');print('RECEIPT',json.dumps({k:record.get(k) for k in ['attempt','exit','wall_seconds','peak_rss_bytes','swaps','accepted']}),flush=True)
sys.exit(0 if record['accepted'] else 1)
