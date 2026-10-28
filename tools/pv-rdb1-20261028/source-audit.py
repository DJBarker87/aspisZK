"""Fresh installed-source pins for every attributed reached library body.
Unresolved symbols stay unresolved; hashes are not semantic proofs.
"""
from pathlib import Path
import json,lzma,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb1-20261028');F=D.parent/'codex-pv-fscan-20261028'
rows=json.loads((D/'prior-rows.json').read_text());functions=json.loads(lzma.decompress((F/'classify-functions.json.xz').read_bytes()))
S=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust')
records=[];mismatches=[]
for row in rows:
 result=[]
 for item in row['reached_source_inventory']:
  fn=item['function'];detail=functions.get(fn,{})
  deps=detail.get('candidates',{}).get('deployed',[])
  checks=[]
  for pin in deps:
   key=pin['key']
   if not key.startswith('deployed/library/'):continue
   p=S/key[len('deployed/'):];h=hashlib.sha256(p.read_bytes()).hexdigest()
   ok=h==pin['file_sha256'];check=dict(path=str(p),sha256=h,pinned=pin['file_sha256'],ok=ok,line=pin['line'],end_line=pin['end_line']);checks.append(check)
   if not ok:mismatches.append(dict(row=row['id'],function=fn,check=check))
  result.append(dict(function=fn,source_class=item['source_class'],installed_std_checks=checks,unresolved=not checks and not fn.startswith(('aspis_','zeroize::'))))
 records.append(dict(row=row['id'],reached=result,prior_residuals=row['residuals']))
out=dict(toolchain='1.94.1',records=records,mismatches=mismatches,meaning='Fresh installed-file verification of attributed bodies only. No resolution of conservative edges and no semantic transfer from a file hash.')
(D/'source-audit.json').write_text(json.dumps(out,indent=2));print('rows',len(rows),'attributed source checks',sum(len(y['installed_std_checks']) for x in records for y in x['reached']),'mismatches',len(mismatches));assert not mismatches,mismatches
