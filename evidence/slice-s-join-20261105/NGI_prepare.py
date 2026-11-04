from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent;P=E.parent
A=P/'slice-s-retarget2-20261104';B=P/'slice-s-retarget3-20261104';F=P/'slice-s-retarget-20261104'
J=lambda p:json.loads(p.read_text())
H=lambda b:hashlib.sha256(b).hexdigest()
# Inputs remain pinned once; original records retained without renaming.
inputs={}
for folder,names in [(A,['NGE_EXPORT.json','NGE_PROVENANCE.json','NGE_AUDIT_ROOTS.json','NGE_LEDGER_DELTA.json']),(B,['NGF_EXPORT.json','NGF_PROVENANCE.json','NGF_AUDIT_ROOTS.json','NGF_LEDGER_DELTA.json','NGF_CERT_INVENTORY.json.xz']),(F,['NFY_AUDIT_ROOTS.json'])]:
 for n in names:inputs[str(folder/n)]={'sha256':H((folder/n).read_bytes()),'bytes':(folder/n).stat().st_size}
(E/'NGI_INPUT_PINS.json').write_text(json.dumps(inputs,indent=1)+'\n')
roots=sorted(set(J(A/'NGE_AUDIT_ROOTS.json')['roots'])|set(J(B/'NGF_AUDIT_ROOTS.json')['roots']))
mods=['NGE_COMBINED_IMPORT','NGF_COMBINED_IMPORT']
(E/'NGI_COMBINED_IMPORT.lean').write_text(''.join('import '+m+'\n' for m in mods)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
# Thirty slots: import/drivers/link 5; fixtures/scan 2; raw partitions 16;
# certificate inventory driver 1 and five parts; root quotations 1.
(E/'NGI_AUDIT_ROOTS.json').write_text(json.dumps(dict(headline='AspisR1.RPx_Deployed.deployed',imports=mods,roots=roots,groups=[roots[i*len(roots)//16:(i+1)*len(roots)//16] for i in range(16)]),indent=1)+'\n')
for name in ['ProofDriver','Driver']:
 s=(B/('NGF_'+name+'.lean')).read_text();t=s.replace('NGF_','NGI_');(E/('NGI_'+name+'.lean')).write_text(t)
 import difflib
 (E/('NGI_'+name+'.diff')).write_text(''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='NGF_'+name+'.lean',tofile='NGI_'+name+'.lean')))
tables={}
for folder,pre in [(A,'NGE'),(B,'NGF')]:
 for l in (folder/(pre+'_EXPECTED_IMPORTS.jsonl')).read_text().splitlines():
  j=json.loads(l);n=j['module']
  if n in tables:assert tables[n]==j['imports'],n
  tables[n]=j['imports']
for f in E.glob('NGI_*.lean'):tables[f.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',f.read_text(),re.M)))
(E/'NGI_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=v))+'\n' for n,v in sorted(tables.items())))
(E/'NGI_batch.py').write_text((B/'NGF_batch.py').read_text().replace('NGF_','NGI_'))
s=(B/'NGF_run.py').read_text().replace('NGF_','NGI_').replace('codex-cx-slice-s-retarget3','codex-cx-slice-s-join').replace('<=110','<=30')
s=s.replace("C+'/NFY_exports_20261104'","C+'/NGE_exports_20261104',C+'/NGF_exports_20261104',C+'/NFY_exports_20261104'")
s=s.replace("if target in ['NGI_Driver','NGI_ProofDriver','NGI_InventoryDriver']:","if target in ['NGI_Driver','NGI_ProofDriver']:")
# Existing client used a separate cache name from workspace name.
s=s.replace("codex-cx-slice-s-join-20261104","codex-cx-slice-s-join-20261105").replace("codex-cx-slice-s-join-cache-20261104","codex-cx-slice-s-join-cache-20261104")
s=s.replace("'/home/dombarker/project-offloads/codex-cx-slice-q-accum-cache-20261104/NFS_native_20261104/'","C+'/NGI_native_seed/'")
(E/'NGI_run.py').write_text(s)
# Whole cache is unnecessary: copy only predecessor selected fallbacks plus exports.
closure=json.loads(lzma.decompress((B/'NGF_CLOSURE_PINS.json.xz').read_bytes()))
files=[]
old='/home/dombarker/project-offloads/codex-cx-slice-s-retarget3-cache-20261104/'
for r in closure['selected_objects']:
 p=r['path']
 if p.startswith(old):files.append(dict(source=p,relative=p[len(old):],sha256=r['sha256'],bytes=r['bytes']))
for folder,pre in [(A,'NGE'),(B,'NGF')]:
 for r in J(folder/(pre+'_EXPORT.json'))['exports']:
  p=r['path'];component=pre+'_exports_20261104/'
  if component in p:files.append(dict(source=p,relative=component+p.split(component)[1],sha256=r['sha256'],bytes=r['bytes']))
# Native walker/limit C inputs are pinned by predecessor export, not rebuilt.
for r in J(B/'NGF_EXPORT.json')['exports']:
 if Path(r['path']).name in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
  files.append(dict(source=r['path'],relative='NGI_native_seed/'+Path(r['path']).name,sha256=r['sha256'],bytes=r['bytes']))
raw=json.dumps(files).encode();(E/'NGI_SEED_INPUTS.json.xz').write_bytes(lzma.compress(raw));(E/'NGI_SEED_INPUTS.json.sha256').write_text(H(raw)+'\n')
print(json.dumps(dict(roots=len(roots),seed_paths=len(files),seed_bytes=sum(f['bytes'] for f in files))))
