from pathlib import Path
import json,hashlib,re
H=Path('/home/dombarker/project-offloads/codex-pv-op254-20261027')
S=H/'lean';O=H/'lean-objects'
records={r['module']:r for r in json.loads((H/'project-sources.json').read_text())}
receipts={}
for f in (H/'lean-receipts').glob('*/receipt.json'):
 r=json.loads(f.read_text())
 if r['charged'] and r['exit']==0:receipts.setdefault(r['module'],[]).append(r)
seen=set();rows=[];externals=set()
def sha(p):return hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
def visit(m):
 if m in seen:return
 seen.add(m)
 if m in ['Aeneas','Std']:
  externals.add(m);return
 assert m in records,('unresolved source authority',m)
 source=S/(m.replace('.','/')+'.lean');obj=O/(m.replace('.','/')+'.olean')
 assert source.exists() and obj.exists(),('missing private source/object',m)
 r=records[m];actual=sha(source);assert actual==r['sha256'],('source pin mismatch',m)
 runs=[x for x in receipts.get(m,[]) if x['source_sha256']==actual];assert runs,('no accepted source-matching receipt',m)
 run=max(runs,key=lambda r:r['attempt'])
 for dep,d in run['dependencies'].items():
  assert sha(Path(d['path']))==d['sha256'],('object dependency changed',m,dep)
 for d in re.findall(r'^import (\S+)',source.read_text(),re.M):visit(d)
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b',source.read_text()),('forbidden token',m)
 assert not re.search(r'^\s*axiom\s',source.read_text(),re.M),('axiom declaration',m)
 rows.append(dict(module=m,**{k:r[k] for k in ['path','blob','revision']},source_sha256=actual,object_sha256=sha(obj),accepted_attempt=run['attempt']))
roots=['PV_B1_Close254','PV_B1_Close230','PV_B1_Close258','PV_B1_PoleWitnesses','PV_B1_ActualContext','PV_B1_PreservedCallbacks','PV_B1_Fidelity','PV_B1_Shift31','PV_B1_MaskShift']
for m in roots:visit(m)
result=dict(roots=roots,project_modules=len(rows),external_roots=sorted(externals),project_objects=rows,status='all frozen sources, private objects and accepted import hashes match; no project objects borrowed')
(H/'closure-preflight.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='project_objects'}))
