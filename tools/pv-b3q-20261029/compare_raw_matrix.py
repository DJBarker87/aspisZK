from pathlib import Path
import json,hashlib,re,ast
H=Path('/home/dombarker/project-offloads/codex-pv-b3q-20261029');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();model={};chain=[]
for chunk in range(2):
 m='PV_B3Q_MatrixRawFixture'+str(chunk);source=H/'lean'/(m+'.lean');rows=[]
 for p in H.glob('lean-*/receipt/receipt.json'):
  r=json.loads(p.read_text())
  if r.get('module')==m and r['exit_status']==0 and r['source_sha256']==sha(source):rows.append((p,r))
 assert len(rows)==1,(m,rows)
 p,r=rows[0];chain.append(dict(module=m,attempt=r['attempt'],source_sha256=sha(source),stdout_sha256=sha(p.parent/'stdout.log')))
 for line in (p.parent/'stdout.log').read_text().splitlines():
  if line.startswith('"raw_matrix:'):
   case,values=json.loads(line).split(':',1)[1].split('=',1);model[int(case)]=json.loads(values)
p=H/'native-matrix-positive/receipt/receipt.json';r=json.loads(p.read_text());assert r['exit_status']==0;actual={}
for line in (p.parent/'stdout.log').read_text().splitlines():
 match=re.fullmatch(r'case=(\d+) matrix=(.*)',line)
 if match:actual[int(match[1])]=sum(ast.literal_eval(match[2]),[])
assert set(actual)==set(model)==set(range(10))
mismatches=[dict(case=i,native=actual[i],emitted=model[i])for i in model if actual[i]!=model[i]]
x=dict(status='pass'if not mismatches else'COUNTEREXAMPLE',matrices=10,entries=90,mismatches=mismatches,model_chain=chain,native_receipt_sha256=sha(p),native_stdout_sha256=sha(p.parent/'stdout.log'),values=model,evidence_class='finite direct native-source private-matrix versus exact emitted-model comparison, including noncanonical raw U32 limbs; compiler V370 and D381,D386 retained')
(H/'matrix-raw-emission-comparison.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x));raise SystemExit(bool(mismatches))
