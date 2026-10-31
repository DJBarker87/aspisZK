from pathlib import Path
import json,hashlib,re
D=Path('evidence/pv-b3q2-20261031');H=D/'host';receipts=[]
for p in H.glob('lean-*/receipt/receipt.json'):
 r=json.loads(p.read_text());receipts.append(r)
assert len(receipts)==77,len(receipts)
rows=[]
for p in sorted((D/'lean').glob('*.lean')):
 sha=hashlib.sha256(p.read_bytes()).hexdigest();rs=[r for r in receipts if r.get('module')==p.stem and r['exit_status']==0 and r['source_sha256']==sha]
 assert rs,('no accepted matching source',p)
 s=p.read_text();ns=re.search(r'^namespace (\S+)',s,re.M);names=[]
 for m in re.finditer(r'^theorem (\w+)',s,re.M):names.append((ns[1]+'.'if ns else'')+m[1])
 for n in names:assert '#print axioms '+n.split('.')[-1]in s or '#print axioms '+n in s,n
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b|maxHeartbeats|maxRecDepth',s,re.M),p
 rows.append(dict(module=p.stem,path=str(p),sha256=sha,attempt=rs[-1]['attempt'],theorems=names))
assert len(rows)==69,len(rows)
(D/'frozen-manifest.json').write_text(json.dumps(dict(focused=rows,theorem_count=sum(len(r['theorems'])for r in rows),planned_audits=[77097,77098,77099],full_manifest_replays=0,limit='accepted local prerequisites/partial family only; no complete op227 source/caller certificate'),indent=2)+'\n')
O=D/'lean'
s=''.join('import '+r['module']+'\n'for r in rows)
s+='#check PV_B3Q_PartialCatalogue2.partial_dependency_link\n#print axioms PV_B3Q_PartialCatalogue2.partial_dependency_link\n'
(O/'PV_B3Q_Resume2Combined.lean').write_text(s)
s='import PV_B3Q_Resume2Combined\n'+''.join('#print axioms '+n+'\n'for r in rows for n in r['theorems'])
(O/'PV_B3Q_Resume2Axioms.lean').write_text(s)
s='import PV_B3Q_Resume2Axioms\n'+''.join('#check '+n+'\n'for r in rows for n in r['theorems'])
s+='#print axioms PV_B3Q_PartialCatalogue2.joint_instance\n'
(O/'PV_B3Q_Resume2Manifest.lean').write_text(s)
print(json.dumps(dict(focused=len(rows),theorems=sum(len(r['theorems'])for r in rows))))
