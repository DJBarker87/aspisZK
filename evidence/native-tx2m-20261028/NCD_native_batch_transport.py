from pathlib import Path
import json,subprocess,sys,time,hashlib,base64,zlib,re
from NCD_expected import expected
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-tx2m-20261028';mode,tag=sys.argv[1:3]
def rpc(code,submitted=False):
 for trial in range(11):
  r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
  with (E/'NCD_NATIVE_BATCH_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(mode=mode,tag=tag,trial=trial,submitted=submitted,exit=r.returncode,stdout=r.stdout,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if trial<10:time.sleep(60)
 raise SystemExit('STOP persistent transport failure')
if mode=='prepare':
 patch=E/'NCD_pair_split.patch';validated=expected(patch);cfg=json.loads((E/'NCD_K006.json').read_text());rows=[]
 for i,name in enumerate(['request_advance','block_cell','advance_cell','block_frame','advance_frame','state','metadata'],7):
  a=f'NCD_K{i:03d}';c=json.loads(json.dumps(cfg));c['attempt']=a;c['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();j=c['command'].index('--harness')+1;c['command'][j]='transcript::NCD_query_pair::'+name;c['expected_time']='optimized native query pair '+name
  c['deps_fingerprint']['matching_copy_negative_control']='NCD_K005';rows.append(dict(cfg=c))
 assert sum(bool(re.fullmatch(r'NCD_K[0-9]+\.json',p.name)) for p in E.iterdir())+len(rows)<=50
 plan=dict(scratch=B+'/NCD_src',rows=rows,source_manifest=validated['after'],source_check=validated,runner=(E/'NCD_native_batch_host.py').read_text())
 (E/('NCD_native_'+tag+'_plan.json')).write_text(json.dumps(plan,indent=2)+'\n')
elif mode=='submit':
 assert not (E/'NCD_BATCH_ACTIVE').exists() and not (E/'NCD_NATIVE_BATCH_ACTIVE').exists()
 plan=json.loads((E/('NCD_native_'+tag+'_plan.json')).read_text());assert sum(bool(re.fullmatch(r'NCD_K[0-9]+\.json',p.name)) for p in E.iterdir())+len(plan['rows'])<=50,'budget reserved by earlier scopes';blob=base64.b64encode(zlib.compress(json.dumps(plan).encode())).decode()
 code=f'''from pathlib import Path
import subprocess,json,zlib,base64,sys
b=Path({B!r});p=b/{('NCD_native_'+tag+'_initial_reservation.json')!r}
with (b/{('NCD_native_'+tag+'_initial_barrier.log')!r}).open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
a=json.loads(p.read_text());print(json.dumps(a),flush=True)
if r.returncode!=0 or a.get('allowed') is not True:sys.exit(r.returncode if r.returncode else 78)
x=json.loads(zlib.decompress(base64.b64decode({blob!r})));assert not (b/{('NCD_native_'+tag+'_submitted.json')!r}).exists(),'never resubmit'
import hashlib
s=Path(x['scratch']);validation=x['source_check']
def drift(expected):return [n for n,h in expected.items() if not (s/n).is_file() or hashlib.sha256((s/n).read_bytes()).hexdigest()!=h]
already=not drift(validation['after']);assert already or not drift(validation['before']),('scratch before drift',drift(validation['before']))
if not already:
 q=b/{('NCD_native_'+tag+'_harness.patch')!r};q.write_text(x['patch']);r=subprocess.run(['git','apply',str(q)],cwd=s,capture_output=True,text=True);assert r.returncode==0,r.stdout+r.stderr
assert not drift(validation['after']),('scratch after drift',drift(validation['after']))
(b/'NCD_native_batch_host.py').write_text(x['runner']);(b/{('NCD_native_'+tag+'_plan.json')!r}).write_text(json.dumps(x,indent=2)+'\\n')
'''
 for retry in range(11):
  r=rpc(code)
  if r.returncode==0:break
  if r.returncode==78 and retry<10:time.sleep(180);continue
  raise SystemExit('STOP native batch setup '+r.stdout+r.stderr)
 launch=f'''from pathlib import Path
import subprocess,json,time
b=Path({B!r});m=b/{('NCD_native_'+tag+'_submitted.json')!r};assert not m.exists(),'never submit twice'
with (b/{('NCD_native_'+tag+'.log')!r}).open('wb') as f:p=subprocess.Popen(['python3','NCD_native_batch_host.py',{tag!r}],cwd=b,stdin=subprocess.DEVNULL,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
m.write_text(json.dumps(dict(pid=p.pid,utc=time.time())));print(m.read_text())
'''
 (E/'NCD_NATIVE_BATCH_ACTIVE').write_text(tag+'\n');r=rpc(launch,submitted=True);print(r.returncode,r.stdout,r.stderr)
elif mode=='recover':
 code=f'''from pathlib import Path
import json,base64
b=Path({B!r});state=b/{('NCD_native_'+tag+'_state.json')!r};names=[{('NCD_native_'+tag+'_state.json')!r},{('NCD_native_'+tag+'.log')!r},{('NCD_native_'+tag+'_submitted.json')!r},{('NCD_native_'+tag+'_initial_reservation.json')!r}]
if state.exists():
 for row in json.loads(state.read_text())['report']:
  a=row['attempt'];names += [a+'.json',a+'-reservation.json',a+'-launcher.log',a+'-graph-check.json',a+'-graph.stderr',a+'-graph-full.json.xz',a+'-graph-full.sha256',a+'-lock-before.log',a+'-lock-after.log',a+'-solver-cleanup.json',a+'/receipt.json',a+'/stdout.log',a+'/time.log']
print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode() for n in names if (b/n).is_file()}}))
'''
 r=rpc(code);assert r.returncode==0,r.stderr;out=json.loads(r.stdout)
 for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(s))
 p=E/('NCD_native_'+tag+'_state.json');state=json.loads(p.read_text()) if p.exists() else {};print(json.dumps(state))
 if state.get('status')=='terminal':(E/'NCD_NATIVE_BATCH_ACTIVE').unlink(missing_ok=True)
 known={json.loads(l)['attempt'] for l in (E/'NCD_ATTEMPTS.jsonl').read_text().splitlines()}
 with (E/'NCD_ATTEMPTS.jsonl').open('a') as f:
  for n in out:
   if n.endswith('/receipt.json'):
    rc=json.loads((E/n).read_text())
    if rc['attempt'] not in known:f.write(json.dumps(rc)+'\n')
else:raise SystemExit('unknown mode')
