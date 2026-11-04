"""Copy selected cache inputs once; never alter a predecessor cache."""
from pathlib import Path
import shutil,hashlib,json,lzma
P=Path('/home/dombarker/project-offloads');C=P/'codex-cx-ledger7-cache-20261104';B=P/'codex-cx-ledger7-20261104';W=P/'codex-cx-sound-int2-20261025'
B.mkdir(exist_ok=True);C.mkdir(exist_ok=True)
a=P/'codex-cx-slice-q-accum-cache-20261104';s=P/'codex-cx-slice-s-compose12-cache-20261104';d=P/'codex-cx-slice-d-define-cache-20261104'
roots=[a/'NFS_exports_20261104',P/'codex-cx-slice-q-phase-cache-20261104/NFN_exports_20261104',P/'codex-cx-slice-q-mul9-cache-20261104/NFM_exports_20261104',P/'codex-cx-slice-q-compose6-cache-20261104/NFG_exports_20261104',s/'NFJ_final_objects_20261104',d/'NFQ_exports_20261104']
roots += [a/n for n in ['NFP_exports_20261104','NFI_exports_20261104','NFF_exports_20261104','NFC_exports_20261104','NFA_exports_20261104','NFG_NFF_objects','NFB_exports_20261104','NEW_exports_20261104','NET_exports_20261104','NFG_standard_view']]
roots += [a,a/'NEB_exports_20261029',a/'NET_peer_exports',a/'NEV_exports_20261104',a/'NEI_exports_20261103',a/'NEG_results_20261101',a/'NEG_exports_20261029',a/'NFB_reconcile_objects',a/'NER_cohort',a/'NFE_exports_20261104',a/'NFC_audit_support_20261104']
roots += [s/n for n in ['NEY_final_objects_20261104','NEX_final_objects_20261104','NEQ_final_objects_20261103','NEM_final_objects_20261102']]+[s,P/'codex-cx-leaf-cache-20261027',P/'codex-cx-cpilot-cache-20261028/NCO_objects',P/'codex-cx-cpilot-cache-20261028']
selected={};pins=[];missing=[]
for root in roots:
 if not root.is_dir():
  if root in roots[:6]:raise FileNotFoundError(root)
  missing.append(str(root));continue
 # Top-level module files and namespace subdirectories; skip nested duplicate caches.
 paths=[p for p in root.rglob('*') if p.is_file() and any(p.name.endswith(x) for x in ['.olean','.olean.private','.olean.server','.ir','.lean','.c']) and not any(('cache' in x or 'exports' in x or x.endswith('_objects') or x.endswith('_cohort') or x.endswith('_view') or x.startswith('NFS_native')) for x in p.relative_to(root).parts[:-1])]
 for p in sorted(paths):
  rel=p.relative_to(root)
  if str(rel) in selected:continue
  dest=C/rel;dest.parent.mkdir(parents=True,exist_ok=True)
  if dest.exists():assert dest.read_bytes()==p.read_bytes(),str(dest)
  else:shutil.copy2(p,dest)
  digest=hashlib.sha256(dest.read_bytes()).hexdigest();selected[str(rel)]=str(p)
  pins.append(dict(source=str(p),destination=str(dest),sha256=digest,bytes=dest.stat().st_size))
raw=json.dumps(dict(roots=[str(r) for r in roots],absent_optional_search_paths=missing,selected=pins),sort_keys=True).encode()
(B/'NFX_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NFX_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
for name in ['S2W_run_host.py','S2W_lean_host.py']:
 shutil.copy2(W/name,B/name)
print(json.dumps(dict(files=len(pins),bytes=sum(r['bytes'] for r in pins),sha256=hashlib.sha256(raw).hexdigest())))
