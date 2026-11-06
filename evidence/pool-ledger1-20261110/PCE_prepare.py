"""Prepare immutable input maps; never launch proofs or write sibling trees."""
from pathlib import Path
import json,lzma,re,hashlib
E=Path(__file__).resolve().parent;R=E.parent
read=lambda p:json.loads(lzma.decompress(p.read_bytes()) if p.suffix=='.xz' else p.read_bytes())
write=lambda n,x:(E/n).write_text(json.dumps(x,indent=1)+'\n')
# Latest canonical header map takes priority over predecessor variants.
expected={};variants=[]
for d,n in [('pc-deposit-pilot-20261110','PCA_EXPECTED_IMPORTS.jsonl'),('pc-helpers1-20261110','PCB_EXPECTED_IMPORTS.jsonl'),('ledger23-20261110','NLS_EXPECTED_IMPORTS.jsonl')]:
 for l in (R/d/n).read_text().splitlines():
  x=json.loads(l);m=x['module']
  if m in expected and expected[m]!=x:variants.append(dict(module=m,old=expected[m],selected=x))
  expected[m]=x
pcb=(R/'pc-helpers1-20261110/PCB_COMBINED_IMPORT.lean').read_text();pca=(R/'pc-deposit-pilot-20261110/PCA_COMBINED_IMPORT.lean').read_text()
imports=list(dict.fromkeys(['RPx_Deployed','NLS_COMBINED_IMPORT','NLF_SdkBorrowLaw']+re.findall(r'^import (\S+)',pcb+'\n'+pca,re.M)))
imports.remove('NLG_COMBINED_IMPORT') # ledger23 includes it transitively; do not replace its receipt module.
roots=list(dict.fromkeys(read(R/'pc-helpers1-20261110/PCB_AUDIT_ROOTS.json')['roots']+read(R/'pc-deposit-pilot-20261110/PCA_AUDIT_ROOTS.json')['groups'][0]))
(E/'PCE_COMBINED_IMPORT.lean').write_text(''.join('import '+m+'\n' for m in imports)+''.join('#print axioms '+r+'\n' for r in roots))
expected['PCE_COMBINED_IMPORT']=dict(module='PCE_COMBINED_IMPORT',imports=['Init']+imports)
closure=set()
def visit(m):
 if m in closure:return
 closure.add(m)
 assert m in expected,('missing expected header',m)
 for i in expected[m]['imports']:visit(i)
visit('PCE_COMBINED_IMPORT')
for m in ['NFA_WALKER','NFA_MemoryLimit','NEP_Planted','NEP_Mutations']:visit(m)
write('PCE_ROOTS.json',dict(roots=roots,pcb=read(R/'pc-helpers1-20261110/PCB_AUDIT_ROOTS.json')['roots'],pca=read(R/'pc-deposit-pilot-20261110/PCA_AUDIT_ROOTS.json')['groups'][0]))
write('PCE_MODULES.json',sorted(closure));write('PCE_HEADER_VARIANTS.json',variants)
(E/'PCE_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(expected[m])+'\n' for m in sorted(closure)))
pins=read(R/'ledger23-20261110/NLS_CLOSURE_PINS.json.xz');seed=[]
for v in pins['selected_objects']:
 if v['module'] not in closure:continue
 v=v.copy();stem=v['module'].replace('.','/');path=v['path'];idx=path.rfind(stem+'.olean')
 rel=stem+'.ir' if idx<0 else path[idx:]
 v['relative']=rel
 if '/codex-cx-ledger23-20261110/NLS_objects/' in path:
  v['path']=path.replace('/codex-cx-ledger23-20261110/NLS_objects/','/codex-cx-ledger8-cache-20261104/NLS_20261110/NLS_exports_20261110/')
 seed.append(v)
# Explicit exports supplement missing canonical inputs only.
pcbexport=read(R/'pc-helpers1-20261110/PCB_EXPORT_MANIFEST.json')
for v in pcbexport['objects']:
 if '/PCB_objects/' not in v['path']:continue
 rel=v['path'].split('/PCB_objects/')[1];m=rel.split('.olean')[0].removesuffix('.ir').replace('/','.')
 if m in closure and not any(z['relative']==rel for z in seed):seed.append(dict(v,module=m,relative=rel))
write('PCE_SEED_REQUEST.json',dict(files=seed,closure=sorted(closure),pca_seed=read(R/'pc-deposit-pilot-20261110/PCA_SEED.json'),extra_search=['/home/dombarker/project-offloads/codex-pc-helpers1-cache-20261110','/home/dombarker/project-offloads/codex-pc-deposit-pilot-cache-20261110/PCA_objects','/home/dombarker/project-offloads/codex-pc-deposit-pilot-cache-20261110/NIZ_seed','/home/dombarker/project-offloads/codex-pc-deposit-pilot-cache-20261110/NIO_seed','/home/dombarker/project-offloads/codex-cx-sdk-borrow-20261109/NLF_exports_20261109_72e6c5ce1014']))
# Reuse NFX duplicate-aware scanner and NEP raw walker, changing only driver names/paths.
s=(R/'pc-helpers1-20261110/PCB_AuditDriver.lean').read_text().replace('PCB_','PCE_')
(E/'PCE_AuditDriver.lean').write_text(s)
write('PCE_PREPARATION.json',dict(modules=len(closure),roots=len(roots),seed_files=len(seed),source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in E.glob('PCE_*.lean')}))
print(f'Prepared {len(closure)} modules and {len(roots)} raw roots; no scopes launched.')
