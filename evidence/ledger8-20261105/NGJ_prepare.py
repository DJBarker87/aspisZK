from pathlib import Path
import json,lzma,hashlib,re
E=Path(__file__).resolve().parent; P=E.parent
J=lambda p:json.loads(p.read_text()); H=lambda b:hashlib.sha256(b).hexdigest()
I=P/'slice-s-join-20261105';files=[]
closure=J(I/'NGI_EXPORT.json')
c=json.loads(lzma.decompress((I/'NGI_CLOSURE_PINS.json.xz').read_bytes()))
old='/home/dombarker/project-offloads/codex-cx-slice-s-join-cache-20261104/'
for r in c['selected_objects']:
 if r['path'].startswith(old):files.append(dict(source=r['path'],relative=r['path'][len(old):],sha256=r['sha256'],bytes=r['bytes']))
for folder,name,key,component in [('slice-s-join-20261105','NGI_EXPORT.json','exports','NGI_exports_20261105/'),('slice-d-field-20261104','NFT_CACHE_END.json','objects','NFT_exports_20261104/')]:
 for r in J(P/folder/name)[key]:
  if component in r['path']:files.append(dict(source=r['path'],relative=component+r['path'].split(component)[1],sha256=r['sha256'],bytes=r['bytes']))
u=J(P/'slice-d-check-20261104/NFU_CACHE_END.json')
for name,r in u['export_objects'].items():files.append(dict(source=u['exports']+'/'+name,relative='NFU_exports_20261104/'+name,sha256=r['sha256'],bytes=r['bytes']))
for p,r in J(P/'pool-retdata3-20261104/NFV_EXPORTS.json')['exports'].items():
 if '/NFV_final_objects_20261104/' in p:files.append(dict(source=p,relative='NFV_final_objects_20261104/'+p.split('/NFV_final_objects_20261104/')[1],**r))
# Pool fallback objects: copy only modules explicitly resolved in its audited closure.
pool=J(P/'pool-retdata3-20261104/NFV_HOST_PINS.json')
(E/'NGJ_POOL_PIN_SCHEMA.json').write_text(json.dumps(dict(type=str(type(pool)),keys=list(pool)[:10]),indent=1))
# Pin C implementation and fixture objects from NGI exports/seed.
seed=json.loads(lzma.decompress((I/'NGI_CACHE_IMPORTS.json.xz').read_bytes()))['selected']
for r in seed:
 if 'NEP_' in r['relative'] or r['relative'].startswith('NGI_native_seed/'):
  files.append(dict(source=r['destination'],relative=r['relative'].replace('NGI_native_seed/','NGJ_native_seed/'),sha256=r['sha256'],bytes=r['bytes']))
files=list({r['relative']:r for r in files}.values())
raw=json.dumps(files).encode();(E/'NGJ_SEED_INPUTS.json.xz').write_bytes(lzma.compress(raw));(E/'NGJ_SEED_INPUTS.json.sha256').write_text(H(raw)+'\n')
# Reuse owned serial client and unchanged launchers.
s=(I/'NGI_run.py').read_text().replace('NGI_','NGJ_').replace('codex-cx-slice-s-join-20261105','codex-cx-ledger8-20261105').replace('codex-cx-slice-s-join-cache-20261104','codex-cx-ledger8-cache-20261104').replace('<=30','<=40')
s=s.replace("C+'/NGE_exports_20261104'","C+'/NGI_exports_20261105',C+'/NFT_exports_20261104',C+'/NFU_exports_20261104',C+'/NFV_final_objects_20261104',C+'/NGE_exports_20261104'")
(E/'NGJ_run.py').write_text(s)
s=(I/'NGI_seed.py').read_text().replace('NGI_','NGJ_').replace('codex-cx-slice-s-join-20261105','codex-cx-ledger8-20261105').replace('codex-cx-slice-s-join-cache-20261104','codex-cx-ledger8-cache-20261104');(E/'NGJ_seed.py').write_text(s)
mods=['NGI_COMBINED_IMPORT','NFT_STAGE2_IMPORT','NFU_STAGE2_IMPORT','NFV_PoolReturnData']
(E/'NGJ_COMBINED_IMPORT.lean').write_text(''.join('import '+m+'\n' for m in mods)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
print(json.dumps(dict(seed_paths=len(files),seed_bytes=sum(r['bytes'] for r in files),pool_keys=list(pool)[:10])))
