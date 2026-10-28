"""Own serial transport batch; unchanged admission and S2W proof backends."""
from pathlib import Path
import subprocess,json,sys,shlex,time,hashlib,base64,lzma
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-tx1top-20261028';C='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';CACHE='/home/dombarker/project-offloads/codex-cx-tx1top-cache-20261028'
start=int(sys.argv[1]);mods=sys.argv[2:];existing=list(E.glob('NCL_L[0-9][0-9][0-9]/receipt.json'));assert len(existing)+len(mods)<=80
assert not (E/'NCL_ACTIVE.json').exists(),'recover own active attempt first'
base=json.loads((E/'NCL_L038.json').read_text());plans=[]
for i,m in enumerate(mods,start):
 a=f'NCL_L{i:03}';assert not (E/a/'receipt.json').exists();src='NCL_generated/'+m+'.lean';obj=CACHE+'/'+m+'.olean'
 cfg={k:base[k] for k in ['kind','env','expected_time','timeout']};cfg.update(attempt=a,module=m,sources=[src],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NCL_generated','-o',obj,src],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={'scope':'Headline-preloaded replay owners; same proof bodies; pinned coherent/Aeneas objects'})
 text=Path('lean',m+'.lean').read_text();p=E/a/'sources'/src;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text);(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n');plans.append(dict(cfg=cfg,text=text,obj=obj))
code=f'''from pathlib import Path
import subprocess,json,sys,time,hashlib,lzma,base64
b=Path({B!r});plans=json.loads({json.dumps(plans)!r});libcode={(E/'NCL_pin_library.py').read_text()!r};expected=json.loads({(E/'NCL_LIBRARY_RESOLVED_INHERITED.json').read_text()!r})
completed=[];events=[]
for plan in plans:
 cfg=plan['cfg'];a=cfg['attempt'];assert not (b/a).exists(),a
 for retry in range(11):
  p=b/(a+'-barrier-'+str(retry)+'.log')
  with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/(a+'-reservation.json'))],stdout=f,stderr=subprocess.STDOUT)
  q=b/(a+'-reservation.json');ad=json.loads(q.read_text()) if q.exists() else None
  events.append(dict(attempt=a,retry=retry,admission_exit=r.returncode,admission=ad))
  if r.returncode==0 and ad and ad.get('allowed') is True:break
  if ad is None and retry==0:time.sleep(30);continue
  if (r.returncode==78 or (ad and ad.get('allowed') is False)) and retry<10:time.sleep(180);continue
  raise RuntimeError('admission refused/failed without launch '+repr(events[-1]))
 else:raise RuntimeError('admission retries exhausted')
 cfg['reservation_retries']=retry
 q=b/cfg['sources'][0];q.parent.mkdir(parents=True,exist_ok=True);q.write_text(plan['text']);Path(plan['obj']).parent.mkdir(parents=True,exist_ok=True)
 check=subprocess.run(['python3','-',cfg['env']['LEAN_PATH']],input=libcode,capture_output=True,text=True)
 assert check.returncode==0,check.stderr
 assert json.loads(check.stdout)==expected,'resolved Aeneas objects/sidecars changed'
 (b/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\\n')
 with (b/(a+'-launcher.log')).open('w') as f:r=subprocess.run(['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3','S2W_lean_host.py',a+'.json'],cwd=b,stdout=f,stderr=subprocess.STDOUT)
 assert (b/a/'receipt.json').is_file(),'missing terminal receipt; never resubmit '+a
 rc=json.loads((b/a/'receipt.json').read_text());completed.append(a)
 if rc['exit_status']!=0:break
names=[]
for a in completed:
 names += [a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-launcher.log',a+'-reservation.json']
 names += [str(p.relative_to(b)) for p in b.glob(a+'-barrier-*.log')]
out={{n:(b/n).read_text() for n in names if (b/n).is_file()}};out['NCL_LEAN_BATCH_EVENTS_{start}.json']=json.dumps(events,indent=2)+'\\n'
raw=json.dumps(out).encode();print(json.dumps(dict(data=base64.b64encode(lzma.compress(raw,preset=6)).decode(),sha256=hashlib.sha256(raw).hexdigest(),completed=completed)))
'''
# This payload is submitted at most once. After any transport failure recover
# terminal attempt files read-only; never restart the serial payload.
(E/f'NCL_LEAN_BATCH_{start}_submitted.json').write_text(json.dumps(dict(attempts=[p['cfg']['attempt'] for p in plans],source_revision=plans[0]['cfg']['source_revision']),indent=2)+'\n')
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/f'NCL_LEAN_BATCH_{start}_transport.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr),indent=2)+'\n')
if r.returncode!=0:raise SystemExit('Submitted batch transport/setup failure; recover read-only, never resubmit: '+r.stderr)
x=json.loads(r.stdout);raw=lzma.decompress(base64.b64decode(x['data']));assert hashlib.sha256(raw).hexdigest()==x['sha256']
for n,text in json.loads(raw).items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
for a in x['completed']:
 rc=json.loads((E/a/'receipt.json').read_text());
 with (E/'NCL_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
 print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}),flush=True)
 if rc['exit_status']!=0:print((E/a/'stdout.log').read_text()[-12000:])
