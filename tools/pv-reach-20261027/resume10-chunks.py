"""Prepare and launch one lead-authorized topological chunk; no shared writes."""
import pathlib,json,subprocess,sys,hashlib,shlex,datetime,time,base64
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume10';H='/home/dombarker/project-offloads/codex-pv-reach-20261027';host='dombarker@100.108.41.90'
a=int(sys.argv[1]);single=sys.argv[2] if not sys.argv[2].isdigit() else None;idx=int(sys.argv[2]) if single is None else -1;assert 40400<=a<=40499
assert a<40497 or (single and 'Audit' in single)
assert sum(1 for p in E.glob('receipt-[0-9]*.json') if json.loads(p.read_text()).get('modules'))<100
assert str(R)=='/Users/dominic/ZK/.worktrees/pv-reach' and subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/pv-reach-20261027'
assert not json.load(open(E/'h4-verification.json'))['mismatches']
assert not (E/f'used-{a}.json').exists()
rows=json.load(open(E/'project-closure.json'));mapping={r['module']:r for r in rows}
if '--native' in sys.argv:
 for r in json.load(open(E.parent/'resume9/native-project-closure.json')):
  assert r['module'] not in mapping or mapping[r['module']]['sha256']==r['sha256']
  mapping[r['module']]=r
need=json.load(open(E/'build-required.json'));names={r['module'] for r in need}
ordered=[r for r in rows if r['module'] in names];assert len(ordered)==len(need)
assert all(d not in names or next(i for i,r in enumerate(ordered) if r['module']==d)<i for i,r in enumerate(ordered) for d in r['imports'])
chunks=[ordered[i:i+30] for i in range(0,len(ordered),30)]
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();selected=chunks[idx] if single is None else [];sources={}
if single:
 import re
 m=single.replace('/','.')
 if m in mapping:
  row=mapping[m]
 else:
  path='docs/research/v8-r0-zk-20261009/lean/'+m.replace('.','/')+'.lean'
  data=subprocess.check_output(['git','show',rev+':'+path]);blob=subprocess.check_output(['git','rev-parse',rev+':'+path],text=True).strip()
  imports=re.findall(r'^import\s+(\S+)',data.decode(),re.M)
  row=dict(module=m,authority='h5',path=path,revision=rev,blob=blob,sha256=hashlib.sha256(data).hexdigest(),imports=imports)
 mapping[m]=row;selected=[row]

def trans(m,s):
 if m not in mapping and m.startswith('R1Z.PV_RE_'):
  import re
  path='docs/research/v8-r0-zk-20261009/lean/'+m.replace('.','/')+'.lean'
  data=subprocess.check_output(['git','show',rev+':'+path]);blob=subprocess.check_output(['git','rev-parse',rev+':'+path],text=True).strip()
  mapping[m]=dict(module=m,authority='h5',path=path,revision=rev,blob=blob,sha256=hashlib.sha256(data).hexdigest(),imports=re.findall(r'^import\s+(\S+)',data.decode(),re.M))
 for d in mapping.get(m,{}).get('imports',[]):
  if d not in s:s.add(d);trans(d,s)
for row in selected:
 data=subprocess.check_output(['git','show',row['blob']]);assert hashlib.sha256(data).hexdigest()==row['sha256']
 if row['authority']=='h5':
  assert subprocess.check_output(['git','show',rev+':'+row['path']])==data
  row['revision']=rev
 ds=set();trans(row['module'],ds);row['transitive_imports']=sorted(ds);sources[row['module']]=base64.b64encode(data).decode()
plan=dict(source_revision=rev,chunk_index=idx,modules=selected,caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,lean_M=7000))
(E/f'plan-{a}.json').write_text(json.dumps(plan,indent=2)+'\n')
(E/f'used-{a}.json').write_text(json.dumps(dict(attempt=a,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),chunk_index=idx))+'\n')
def ssh(cmd,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh',host,cmd],capture_output=True,text=True)
  if r.returncode!=255:return r
  with (E/'transport-retries.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,submitted=submitted,error=r.stderr))+'\n')
  if retry<10:time.sleep(60)
  if submitted: return r # Recovery is read-only; never resubmit a compile.
 return r
cmd=f'python3 /home/dombarker/project-offloads/codex-cx-s2x-20261023/S2X_reservation.py {H}/evidence/pvre-reservation-{a}.json > {H}/evidence/pvre-reservation-{a}.log 2>&1; admission_status=$?; cat {H}/evidence/pvre-reservation-{a}.log; exit $admission_status'
r=ssh(cmd);(E/f'reservation-{a}.log').write_text(r.stdout+r.stderr)
assert r.returncode in [0,78],r.stderr+r.stdout
admission=json.loads(r.stdout.strip().splitlines()[-1]);(E/f'reservation-{a}.json').write_text(json.dumps(admission,indent=2)+'\n')
if r.returncode!=0 or not admission['allowed']:print('REFUSAL',flush=True);sys.exit(78)
# Source preparation is private and uses the exact pinned bytes; no external objects are copied.
payload=dict(plan=plan,sources=sources);(E/f'payload-{a}.json').write_text(json.dumps(payload))
for src,dst in [(E/f'payload-{a}.json',f'{H}/evidence/resume10-payload-{a}.json'),(R/'tools/pv-reach-20261027/resume10-chunk-host.py',f'{H}/evidence/resume10-chunk-host.py')]:
 for retry in range(11):
  q=subprocess.run(['scp','-q',str(src),host+':'+dst],capture_output=True,text=True)
  if q.returncode!=255:break
  with (E/'transport-retries.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,scp=str(src),error=q.stderr))+'\n')
  if retry<10:time.sleep(60)
 q.check_returncode()
(E/f'payload-{a}.json').unlink() # Bytes are already committed; hashes and blobs are the evidence.
prep=f'''import pathlib,json,base64,hashlib
h=pathlib.Path({H!r});x=json.load(open(h/'evidence/resume10-payload-{a}.json'))
for m,b in x['sources'].items():
 p=h/'lean/sources'/(m.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True)
 if p.is_symlink():p.unlink()
 p.write_bytes(base64.b64decode(b))
(h/'evidence/resume10-plan-{a}.json').write_text(json.dumps(x['plan']))
'''
r=ssh('python3 -c '+shlex.quote(prep));r.check_returncode()
cmd=['systemd-run','--user','--scope','--quiet',f'--unit=pvre-lean-{a}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',f'{H}/evidence/resume10-time-{a}.log','python3',f'{H}/evidence/resume10-chunk-host.py',str(a)]
(E/f'launch-{a}.json').write_text(json.dumps(dict(command=cmd,plan=plan,reservation=admission),indent=2)+'\n')
print('LAUNCH',a,idx,[r['module'] for r in selected],flush=True)
r=ssh(shlex.join(cmd)+f' > {H}/evidence/resume10-out-{a}.log 2>&1',True)
if r.returncode==255:
 for recovery in range(11):
  q=ssh('test -f '+shlex.quote(f'{H}/evidence/resume10-{a}/receipt.json'))
  if q.returncode==0:break
  with (E/'transport-retries.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,recovery=recovery,read_only=True,receipt_pending=True))+'\n')
  if recovery<10:time.sleep(60)
 else:sys.exit(255)
for name,path in [('receipt',f'{H}/evidence/resume10-{a}/receipt.json'),('out',f'{H}/evidence/resume10-out-{a}.log'),('time',f'{H}/evidence/resume10-time-{a}.log')]:
 q=ssh('cat '+shlex.quote(path));(E/(f'{name}-{a}'+('.json' if name=='receipt' else '.log'))).write_text(q.stdout+q.stderr)
print((E/f'out-{a}.log').read_text()[-4000:],flush=True)
result=json.loads((E/f'receipt-{a}.json').read_text())
(E/f'collection-{a}.json').write_text(json.dumps(dict(submission_transport_exit=r.returncode,recovered_without_resubmission=r.returncode==255,receipt_accepted=result['accepted']))+'\n')
sys.exit(0 if result['accepted'] else 1)
