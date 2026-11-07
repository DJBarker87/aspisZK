from NND_transport import *
import hashlib
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
x=json.loads(subprocess.check_output(['git','show','HEAD:evidence/ledger24-20261110/NLX_L005.json'],text=True))
pins={k:v for k,v in x['deps_fingerprint']['selected_objects'].items() if Path(k).name.split('.')[0] in ['NFA_WALKER','NFA_MemoryLimit','NEP_Planted','NEP_Mutations']}
assert all(any(Path(k).name==n+'.olean' for k in pins) for n in ['NFA_WALKER','NFA_MemoryLimit','NEP_Planted','NEP_Mutations'])
r=ssh('python3',f'''from pathlib import Path
import hashlib,json,shutil
pins=json.loads({json.dumps(pins)!r});b=Path({B!r})/'NND_seed';out=[]
for n,pin in pins.items():
 p=Path(n);h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==pin['sha256'],n
 q=b/p.name
 if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
 else:shutil.copy2(p,q)
 out.append(dict(source=n,target=str(q),sha256=h))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
(E/'NND_AUDIT_SUPPORT_IMPORTS.json').write_text(json.dumps({'provenance_revision':rev,'manifest':'evidence/ledger24-20261110/NLX_L005.json','objects':json.loads(r.stdout)},indent=1)+'\n')
print(json.dumps({'copied':len(pins),'hashes_match_ledger24':True}))
