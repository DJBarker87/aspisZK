"""Replay the unchanged f31 and copy cones, with an explicit final-ID reserve."""
import hashlib,json,pathlib,subprocess,sys,time,lzma
E=pathlib.Path('evidence/pv-lib-20261107')
x=json.loads((E/'SESSION2_SLICE_REPLAY_ORDER.json').read_text());rev=x['revision']
queue=x['modules'][:27]+x['modules'][-4:]
for m,_ in queue:
 receipts=[json.loads(q.read_text()) for q in E.glob('receipt-*.json')]
 if any(r['target']==m and r['accepted'] for r in receipts):continue
 p=pathlib.Path('lean',m+'.lean');raw=subprocess.check_output(['git','show',rev+':lean/'+m+'.lean'])
 if p.exists():assert p.read_bytes()==raw,p
 else:p.write_bytes(raw)
 subprocess.run(['git','add','--sparse',str(p)],check=True)
 for retry in range(10):
  for q in E.glob('refusal-*.json'):
   delay=json.loads(q.read_text())['epoch']+181-time.time()
   while delay>0:
    print('COOLDOWN',round(delay),flush=True);time.sleep(min(60,delay));delay=json.loads(q.read_text())['epoch']+181-time.time()
  a=max(int(q.stem.split('-')[-1]) for q in E.glob('turn-*.json') if int(q.stem.split('-')[-1])<49480)+1
  if a>49465:sys.exit('review: preserve final graph/audit-driver IDs49466–49479')
  print('SLICE REPLAY',a,m,flush=True)
  rc=subprocess.run([sys.executable,'tools/pv-lib-20261107/compile.py',str(a),m]).returncode
  files=[str(q) for q in E.glob('*'+str(a)+'*')]
  subprocess.run(['git','add','--sparse',*files],check=True)
  if rc==78:
   subprocess.run(['git','commit','--only',*files,'-m','Record refused PLIB slice replay '+str(a)],check=True);continue
  if rc:
   (E/'failed-sources'/(str(a)+'.lean.xz')).write_bytes(lzma.compress(raw))
   sys.exit('provider replay stopped: '+m)
  subprocess.run(['git','commit','--only',str(p),*files,'-m','Replay pinned slice provider '+m],check=True)
  break
 else:sys.exit('ten admission refusals')
