#!/usr/bin/env python3
"""L187 option-B local driver. Autonomous: schedules dependency-ready batches (<=2 concurrent per lead 2026-11-09, 1 if host lean count is 5, host lean
count < 6, scope count < 6, disk >= 40 GB, admission allowed:true AND exit 0), fetches results,
commits receipts per batch (xz + sha256 sidecar), skips dependants of failures, writes ALERT files."""
import json,subprocess,time,lzma,hashlib,pathlib,sys,collections,os
E=pathlib.Path(__file__).resolve().parent; REPO=E.parents[1]
H='dombarker@100.108.41.90'; W='/home/dombarker/project-offloads/codex-cx-replay-l187-20261109'
S=pathlib.Path('/private/tmp/claude-501/-Users-dominic-ZK/3db59790-41f3-4c53-ae90-3fc42a8cab96/scratchpad')
plan=json.loads((S/'l187_plan.json').read_text()); P=plan['plan']; order=plan['order']
SF=E/'L187_STATE.json'
st=json.loads(SF.read_text()) if SF.exists() else dict(status={m:'pending' for m in order},inflight={},next=1,batches=[],alerts=[])
rev=collections.defaultdict(list)
for m,v in P.items():
  for i in v['imports']: rev[i].append(m)
def save(): SF.write_text(json.dumps(st))
def log(*a):
  with open(E/'L187_DRIVER.log','a') as f: f.write(time.strftime('%Y-%m-%dT%H:%M:%SZ ',time.gmtime())+' '.join(map(str,a))+'\n')
def ssh(code,inp=None,t=300):
  return subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=20',H,code],input=inp,capture_output=True,text=True,timeout=t)
def alert(kind,msg):
  st['alerts'].append(dict(kind=kind,msg=msg,utc=time.time())); (E/('ALERT_'+kind)).write_text(msg+'\n'); log('ALERT',kind,msg)
def git(*a): return subprocess.run(['git','-C',str(REPO),*a],capture_output=True,text=True)
def skip_dependants(m):
  stack=list(rev[m])
  while stack:
    d=stack.pop()
    if st['status'][d] in ('pending',):
      st['status'][d]='SKIPPED_DEP_FAILED:'+m; stack+=rev[d]
def host_state():
  r=ssh("""python3 - <<'PY'
import json,subprocess,shutil,pathlib,glob
root=pathlib.Path('/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice')
pop=0
for p in root.glob('*.scope'):
  try:
    if (p/'cgroup.procs').read_text().strip(): pop+=1
  except FileNotFoundError: pass
lean=subprocess.run(['pgrep','-c','-x','lean'],capture_output=True,text=True).stdout.strip() or '0'
done=[pathlib.Path(x).parent.name for x in glob.glob('%s/batches/*/DONE.json')]
print(json.dumps(dict(scopes=pop,lean=int(lean),free=shutil.disk_usage('%s').free,done=done)))
PY"""%(W,W))
  return json.loads(r.stdout) if r.returncode==0 else None
def collect(b):
  d=E/'batches'/b; d.mkdir(parents=True,exist_ok=True)
  r=ssh(f"cd {W}/batches/{b} && python3 -c \"import json,pathlib;print(json.dumps({{p.name:p.read_text() for p in pathlib.Path('.').iterdir() if p.is_file()}}))\"",t=600)
  files=json.loads(r.stdout)
  for n,t in files.items():
    raw=t.encode()
    if n=='results.jsonl' or len(raw)>200000:
      (d/(n+'.xz')).write_bytes(lzma.compress(raw,preset=6)); (d/(n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n')
    else: (d/n).write_text(t)
  rows=[json.loads(l) for l in files.get('results.jsonl','').splitlines() if l.strip()]
  done=json.loads(files['DONE.json'])
  summ=collections.Counter()
  for row in rows:
    m=row['module'];s=row['status'];summ[s]+=1
    if s=='PASS':
      st['status'][m]='PASS_IDENTICAL' if row.get('object_identical_to_overlay') else 'PASS_DIFFERS'
      if row.get('sorry_warnings'): alert('SORRY',f"{m} in {b}: sorry warning(s)")
    elif s=='FAIL':
      st['status'][m]='FAIL'; skip_dependants(m)
      alert('FAILURE',f"{m} ({row.get('label')}) failed in {b}, exit {row.get('exit')}: "+(row.get('diagnostics_tail') or '')[-1500:])
    else: st['status'][m]='pending'
  ident=sum(1 for r in rows if r.get('object_identical_to_overlay')); diff=sum(1 for r in rows if r['status']=='PASS' and not r.get('object_identical_to_overlay'))
  rec=dict(batch=b,done=done,counts=dict(summ),identical=ident,differs=diff,
    max_rss_kib=max([int(r['peak_rss_kib']) for r in rows if r.get('peak_rss_kib')] or [0]),
    swaps_total=sum(int(r['swaps'] or 0) for r in rows if r.get('swaps') is not None))
  (d/'SUMMARY.json').write_text(json.dumps(rec,indent=1)); st['batches'].append(rec)
  del st['inflight'][b]; save()
  built=sum(1 for v in st['status'].values() if v.startswith('PASS'))
  if built*2>=len(order) and not any(a['kind']=='HALF' for a in st['alerts']): alert('HALF',f'{built} of {len(order)} modules rebuilt')
  git('add','--sparse',str(E)); g=git('commit','-q','-m',f'L187 replay {b}: '+json.dumps(dict(summ))+f'; identical {ident}, differs {diff}')
  log('collected',b,dict(summ),'identical',ident,'differs',diff,'commit rc',g.returncode,g.stderr[:200])
def pick():
  reserved={m for b in st['inflight'].values() for m in b}
  chosen=[];cs=set()
  for m in order:
    if st['status'][m]!='pending' or m in reserved: continue
    if all((st['status'][i].startswith('PASS')) or i in cs for i in P[m]['imports']):
      chosen.append(m); cs.add(m)
      if len(chosen)>=400: break
  return chosen
def launch(mods,hs):
  b='B%04d'%st['next']; st['next']+=1
  batch=dict(batch=b,modules=[dict(module=m,src_rel=P[m]['src_rel'],imports=P[m]['imports'],label=P[m]['label'],source=P[m]['source'],overlay=P[m]['overlay']) for m in mods])
  r=ssh(f"mkdir -p {W}/batches/{b} && cat > {W}/batches/{b}/batch.json",inp=json.dumps(batch))
  if r.returncode!=0: log('upload failed',b,r.stderr[:300]); return False
  a=ssh(f"python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {W}/batches/{b}/reservation.json; echo EXIT=$?")
  ok=a.returncode==0 and 'EXIT=0' in a.stdout and '"allowed": true' in a.stdout
  (E/'batches'/b).mkdir(parents=True,exist_ok=True); (E/'batches'/b/'admission.txt').write_text(a.stdout+a.stderr+'\nhost:'+json.dumps(hs)+'\n')
  if not ok: log('admission refused',b,a.stdout[-300:]); ssh(f"rm -rf {W}/batches/{b}"); st['next']-=1; return False
  subprocess.Popen(['ssh','-n','-o','ControlMaster=no','-o','ConnectTimeout=20',H,f"cd {W} && exec systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 L187_runner.py {b} > batches/{b}/launcher.log 2>&1 < /dev/null"],stdin=subprocess.DEVNULL,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,start_new_session=True)
  time.sleep(5)
  st['inflight'][b]=mods; save(); log('launched',b,len(mods),'first',mods[0],'host',hs); return True
log('driver start',sum(1 for v in st['status'].values() if v=='pending'),'pending')
while True:
  if (E/'STOP').exists(): log('STOP file'); break
  try: hs=host_state()
  except Exception as e: hs=None; log('host_state error',e)
  if hs:
    for b in list(st['inflight']):
      if b in hs['done']:
        try: collect(b)
        except Exception as e: log('collect error',b,repr(e))
    if hs['free']<40_000_000_000:
      if not (E/'ALERT_DISK').exists(): alert('DISK',f"host free {hs['free']} < 40 GB; launches paused")
    else:
      if (E/'ALERT_DISK').exists(): (E/'ALERT_DISK').unlink()
      while len(st['inflight'])<(1 if hs['lean']>=5 else 2) and hs['lean']+1<6 and hs['scopes']+1<6:
        mods=pick()
        if not mods: break
        try: ok=launch(mods,hs)
        except Exception as e: log('launch error',repr(e)); ok=False
        if not ok: break
        hs['lean']+=1; hs['scopes']+=1
  pend=sum(1 for v in st['status'].values() if v=='pending')
  if not st['inflight'] and (pend==0 or not pick()):
    alert('END',json.dumps(collections.Counter(v.split(':')[0] for v in st['status'].values()))); save(); break
  save(); time.sleep(60)
