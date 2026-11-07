"""Serial pinned provider cache extension; one focused scope and commit per module."""
import pathlib,json,subprocess,sys,time,hashlib
A=pathlib.Path('evidence/pv-lib-20261107/lane-A');E=A/'session4'
for item in json.load(open(E/'F6_REPLAY_PLAN.json')):
 m=item['module'];p=item['source_path'];sha=hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest();assert sha==item['source_sha256']
 receipts=[json.load(open(q)) for d in [A,E] for q in d.glob('receipt-*.json')]
 if any(r['accepted'] and r['target']==m and r['source_sha256']==sha for r in receipts):continue
 used=[int(q.stem.split('-')[-1]) for q in E.glob('turn-*.json') if 49100<=int(q.stem.split('-')[-1])<=49199];a=max(used,default=49177)+1
 if a>49198:break
 subprocess.run(['git','add','--sparse',p],check=True)
 print('REPLAY',a,m,flush=True)
 r=subprocess.run([sys.executable,str(A/'compile-s4.py'),str(a),m,p])
 if r.returncode:sys.exit(r.returncode)
 hand=A/'HANDOFF.md';hand.write_text(hand.read_text()+f'\nSession4 {a}: pinned {m} passed; session4 receipt records resources/axioms.\n')
 subprocess.run(['git','add','--sparse',str(E),str(hand),p],check=True)
 subprocess.run(['git','commit','-m','Replay Lane A pinned provider '+m],check=True)
