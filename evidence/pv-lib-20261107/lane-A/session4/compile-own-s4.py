"""Compile each smallest changed library module, committing only passing inputs."""
import pathlib,json,subprocess,sys
A=pathlib.Path('evidence/pv-lib-20261107/lane-A');S=A/'session4'
mods=['PV_LIB_A_OwnerStoreTransport','PV_LIB_A_WriterSites','PV_LIB_A_OwnerStoreActions','PV_LIB_A_RangeWriter','PV_LIB_A_WriterNumbering','PV_LIB_A_Caller124','PV_LIB_A_NameValidity','PV_LIB_A_PrefixTransport']
for m in mods:
 rs=[json.loads(p.read_text()) for p in S.glob('receipt-*.json')]
 if any(r['accepted'] and not r['runtime_audit'] and r['target']==m for r in rs):continue
 used=[int(p.stem.split('-')[-1]) for p in S.glob('turn-*.json') if 49100<=int(p.stem.split('-')[-1])<=49199]
 a=max(used)+1;assert a<49199
 p=pathlib.Path('lean',m+'.lean');subprocess.run(['git','add',str(p)],check=True)
 print('OWN',a,m,flush=True)
 r=subprocess.run([sys.executable,str(A/'compile-s4.py'),str(a),m]);
 if r.returncode:sys.exit(r.returncode)
 hand=A/'HANDOFF.md';hand.write_text(hand.read_text()+f'\nSession4 {a} passed {m}; exact receipt/axioms in session4.\n')
 subprocess.run(['git','add','--sparse',str(S),str(hand),str(p)],check=True)
 subprocess.run(['git','commit','-m','Add Lane A adapter '+m],check=True)
