"""Assemble exact declaration text into a new module, never edit pinned sources."""
from pathlib import Path
import re,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-skwb-20261029')
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=json.loads((D/'remaining-plan.json').read_text());rows=[r for r in rows if not (D/'objects'/(r['module'].replace('.','/')+'.olean')).is_file()]
inside={r['module'] for r in rows};imports=[];blocks=[];manifest=[]
for r in rows:
 p=D/'sources'/(r['module'].replace('.','/')+'.lean');raw=p.read_bytes();assert sha(raw)==r['source_sha256']
 s=raw.decode();imps=re.findall(r'^import (\S+)\s*$',s,re.M)
 for m in imps:
  if m not in inside and m not in imports:imports.append(m)
 body=re.sub(r'^import \S+\s*\n','',s,flags=re.M)
 # Preserve file-level command scopes: each original implicit noncomputable section
 # ends at its old EOF. Explicit namespaces are already balanced in the pinned file.
 nopens=len(re.findall(r'^(?:noncomputable )?section(?:\s+\w+)?\s*$',body,re.M))+len(re.findall(r'^namespace\s+\S+\s*$',body,re.M))
 nends=len(re.findall(r'^end(?:\s+\S+)?\s*$',body,re.M))
 assert nopens>=nends,(r['module'],nopens,nends)
 blocks.append('\nsection\n'+body+'\n'+('end\n'*(nopens-nends))+'end\n')
 manifest.append(dict(module=r['module'],source_sha256=sha(raw),source_path=r['source_path'],body_sha256=sha(body.encode()),implicit_scopes_closed=nopens-nends))
witness=(D/'PV_SKWB_OWNM.lean').read_text();witness=witness.replace('import R1Z.PV_OWNN_SourceDense\n','')
for m in re.findall(r'^import (\S+)\s*$',witness,re.M):
 if m not in imports:imports.append(m)
witness=re.sub(r'^import \S+\s*\n','',witness,flags=re.M)
out=''.join('import '+m+'\n' for m in imports)+'\n'+''.join(blocks)+'\n'+witness
(D/'sources/PV_SKWB_OWNM.lean').write_text(out)
(D/'assembly.json').write_text(json.dumps(dict(policy='exact declaration text; only import lines removed and file-level scopes explicitly closed; skeleton and links imported unchanged',modules=manifest,imports=imports,assembly_sha256=sha(out.encode()),original_witness_sha256=sha(witness.encode())),indent=2)+'\n')
print('assembly',len(rows),'sources',len(out),'bytes',len(imports),'imports')
