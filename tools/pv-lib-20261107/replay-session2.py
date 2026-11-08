"""Replay unchanged pinned provider sources serially; commit every passing compile."""
import hashlib,json,pathlib,re,subprocess,sys,time
E=pathlib.Path('evidence/pv-lib-20261107')
rev='fc0340264851248e164a098c170cc53e22857085'
order=json.loads((E/'SESSION2_REPLAY_ORDER.json').read_text())
manifest=[]
for i,(m,_) in enumerate(order):
 raw=subprocess.check_output(['git','show',rev+':lean/'+m+'.lean'])
 manifest.append(dict(module=m,revision=rev,source_sha256=hashlib.sha256(raw).hexdigest(),planned_order=i))
(E/'SESSION2_REPLAY.json').write_text(json.dumps(manifest,indent=2)+'\n')
subprocess.run(['git','add','--sparse',str(E/'SESSION2_REPLAY.json')],check=True)
for record in manifest:
 m=record['module'];p=pathlib.Path('lean',m+'.lean')
 passed=[json.loads(q.read_text()) for q in E.glob('receipt-*.json')]
 if any(r['target']==m and r['accepted'] for r in passed): continue
 raw=subprocess.check_output(['git','show',rev+':lean/'+m+'.lean'])
 if p.exists(): assert p.read_bytes()==raw,p
 else: p.write_bytes(raw)
 subprocess.run(['git','add','--sparse',str(p)],check=True)
 for retry in range(10):
  for q in E.glob('refusal-*.json'):
   delay=json.loads(q.read_text())['epoch']+181-time.time()
   while delay>0:
    print('COOLDOWN',round(delay),flush=True);time.sleep(min(60,delay));delay=json.loads(q.read_text())['epoch']+181-time.time()
  used=[int(q.stem.split('-')[-1]) for q in E.glob('turn-*.json') if int(q.stem.split('-')[-1])<49480]
  a=max(used)+1
  print('REPLAY',a,m,flush=True)
  rc=subprocess.run([sys.executable,'tools/pv-lib-20261107/compile.py',str(a),m]).returncode
  files=[str(q) for q in E.glob('*'+str(a)+'*')]
  subprocess.run(['git','add','--sparse',*files],check=True)
  if rc==78:
   subprocess.run(['git','commit','--only',*files,'-m','Record refused PLIB replay '+str(a)],check=True);continue
  if rc:
   print('STOP',a,m,rc,flush=True);sys.exit(rc)
  subprocess.run(['git','commit','--only',str(p),*files,'-m','Replay pinned provider '+m],check=True)
  break
 else:sys.exit('ten admission refusals')
