from pathlib import Path
import json,lzma,hashlib,shutil
H=Path(__file__).resolve().parent;A=H.parent/'codex-pv-evhc9-20261104/agg-92080';T=H/'reachable';T.mkdir(exist_ok=False)
roots=json.loads((A/'RAW-AXIOMS.json').read_text())['roots'];rows=[]
for r in roots:
 n='NEP_final_'+r['root']+'_REACHABLE.txt';p=A/n;h=hashlib.sha256();count=0;found=False
 with p.open('rb') as f,lzma.open(T/(n+'.xz'),'wb',preset=6) as out:
  for line in f:
   h.update(line);out.write(line);count+=1;found=found or line.rstrip(b'\n')==r['root'].encode()
 assert count==r['reachable_constants'] and found,(n,count)
 (T/(n+'.sha256')).write_text(h.hexdigest()+'  '+n+'\n')
 rows.append(dict(root=r['root'],file=n+'.xz',uncompressed_sha256=h.hexdigest(),uncompressed_bytes=p.stat().st_size,lines=count,root_present=found))
(T/'MANIFEST.json').write_text(json.dumps(rows,indent=2)+'\n')
print('COMPLETE',len(rows),flush=True)
