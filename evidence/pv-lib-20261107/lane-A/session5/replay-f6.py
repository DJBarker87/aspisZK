"""Serial exact-provider cache completion; no provider source changes."""
import pathlib,json,subprocess,sys,hashlib,time
A=pathlib.Path('evidence/pv-lib-20261107/lane-A');E=A/'session5'
plan=json.load(open(A/'session4/F6_REPLAY_PLAN.json'))
def receipts():
 return [json.load(open(p)) for folder in [A,A/'session4',E] for p in folder.glob('receipt-*.json')]
for item in plan:
 m=item['module'];p=pathlib.Path(item['source_path']);raw=p.read_bytes()
 assert hashlib.sha256(raw).hexdigest()==item['source_sha256'],m
 accepted=[r for r in receipts()if r['accepted']and r['target']==m and not r['runtime_audit']]
 if accepted:
  assert accepted[-1]['source_sha256']==item['source_sha256'];continue
 used={int(q.stem.split('-')[-1])for q in E.glob('turn-*.json')}
 ids=list(range(46300,46400))+list(range(47400,47489)) # reserve47489 for audit driver
 a=next((n for n in ids if n not in used),None)
 if a is None:sys.exit('focused block exhausted; audit driver reserved')
 print('NEXT',a,m,flush=True)
 subprocess.run(['git','add','--sparse',str(p)],check=True)
 r=subprocess.run([sys.executable,str(A/'compile-s5.py'),str(a),m,str(p)])
 if r.returncode:
  (E/'F6_REPLAY_STOP.json').write_text(json.dumps(dict(attempt=a,module=m,exit=r.returncode,source_changed=False),indent=2)+'\n')
  sys.exit(r.returncode)
 h=A/'HANDOFF.md';h.write_text(h.read_text()+f'\n{a} exact pinned f6 provider replay {m} passed; cache preparation only, not caller/transport closure. See receipt.\n')
 files=[str(p),str(h),str(E/'replay-f6.py')]+[str(q)for q in E.glob('*'+str(a)+'*')]
 subprocess.run(['git','add','--sparse',*files],check=True)
 subprocess.run(['git','commit','--only',*files,'-m','Replay exact f6 provider '+m],check=True)
print('F6 CACHE COMPLETE',flush=True)
