#!/usr/bin/env python3
"""Read-only inspection of proc_macro2 fingerprints transitively required by macro dependencies."""
import json, pathlib
root=pathlib.Path('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/charon/target/release')
main=json.loads((root/'.fingerprint/charon-dce94fe66085d37d/bin-charon-driver.json').read_text())
output=[]
for dep_id,name,_,dep_hash in main['deps']:
 if name not in ('macros','hax_adt_into'):
  continue
 pattern='lib-'+name+'.json'
 candidates=[]
 for path in root.joinpath('.fingerprint').glob('*/'+pattern):
  marker=path.parent/('lib-'+name)
  if not marker.is_file(): continue
  value=int.from_bytes(bytes.fromhex(marker.read_text().strip()),'little')
  if value!=dep_hash: continue
  lib=json.loads(path.read_text())
  for nested_id,nested_name,_,nested_hash in lib['deps']:
   if nested_name!='proc_macro2': continue
   hits=[]
   for npath in root.joinpath('.fingerprint').glob('proc-macro2-*/lib-proc_macro2.json'):
    nm=npath.parent/'lib-proc_macro2'
    if not nm.is_file(): continue
    nvalue=int.from_bytes(bytes.fromhex(nm.read_text().strip()),'little')
    if nvalue==nested_hash:
     artprefix='libproc_macro2-'+npath.parent.name.rsplit('-',1)[-1]
     arts=[]
     for a in root.joinpath('deps').glob(artprefix+'.*'):
      if a.suffix in ('.rlib','.rmeta','.so'):
       arts.append({'path':str(a.relative_to(root)),'size':a.stat().st_size})
     nmeta=json.loads(npath.read_text())
     hits.append({'fingerprint_dir':npath.parent.name,'marker':nm.read_text().strip(),'features':nmeta.get('features'),'profile':nmeta.get('profile'),'artifacts':arts})
   candidates.append({'parent_crate':name,'parent_fingerprint_dir':path.parent.name,'nested_hash_u64':nested_hash,'nested_hash_hex':hex(nested_hash),'matching_proc_macro2_units':hits})
 output.extend(candidates)
print(json.dumps({'scan_root':str(root),'parents':output},indent=2,sort_keys=True))
