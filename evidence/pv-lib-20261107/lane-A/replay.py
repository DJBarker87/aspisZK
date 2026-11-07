"""Serial exact pinned provider replay; own lane evidence and host only."""
import pathlib,json,subprocess,sys,time,hashlib
E=pathlib.Path('evidence/pv-lib-20261107/lane-A')
for item in json.load(open(E/sys.argv[1])):
 m=item['module'];p=item['source_path']
 if 'source_sha256' in item:assert hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()==item['source_sha256'],m
 passed=[json.load(open(q)) for q in E.glob('receipt-*.json') if json.load(open(q))['target']==m and json.load(open(q))['accepted']]
 if passed:
  assert passed[-1]['source_sha256']==hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest(),('accepted source differs',m)
  continue
 subprocess.run(['git','add','--sparse',p],check=True)
 for retry in range(10):
  for q in E.glob('refusal-*.json'):
   delay=json.load(open(q))['epoch']+181-time.time()
   while delay>0:
    print('COOLDOWN',round(delay),flush=True);time.sleep(min(45,delay));delay=json.load(open(q))['epoch']+181-time.time()
  used=[int(q.stem.split('-')[-1]) for q in E.glob('turn-*.json') if int(q.stem.split('-')[-1])<49480 or 49800<=int(q.stem.split('-')[-1])<=49889]
  a=max(used)+1
  if a==49480:a=49800
  if len(sys.argv)>2 and a>int(sys.argv[2]):
   subprocess.run(['git','restore','--staged','--',p],check=True)
   (E/'BUDGET_REPLAY_STOP.json').write_text(json.dumps(dict(next_module=m,next_attempt=a,reserved_for_audit_driver=True,plan=sys.argv[1]),indent=2)+'\n')
   print('RESERVED AUDIT DRIVER',a,m,flush=True);sys.exit(0)
  assert 49458<=a<=49479 or 49800<=a<=49889
  print('REPLAY',a,m,flush=True)
  r=subprocess.run([sys.executable,str(E/'compile.py'),str(a),m,p])
  files=[str(q) for q in E.glob('*'+str(a)+'*')]
  if r.returncode==78:
   subprocess.run(['git','add','--sparse',*files],check=True)
   subprocess.run(['git','commit','--only',*files,'-m','Record Lane A refusal '+str(a)],check=True);continue
  if r.returncode:sys.exit(r.returncode)
  hand=E/'HANDOFF.md';hand.write_text(hand.read_text()+f'\n{a} passed exact pinned replay {m}; see receipt for time/RSS/swap/revision/axioms.\n')
  files += [p,str(hand),str(E/'compile.py'),str(E/'replay.py'),str(E/sys.argv[1])]
  subprocess.run(['git','add','--sparse',*files],check=True)
  subprocess.run(['git','commit','--only',*files,'-m','Replay Lane A pinned provider '+m],check=True)
  break
 else:sys.exit('ten refusals')
