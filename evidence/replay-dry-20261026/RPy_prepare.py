"""Prepare sources and per-module configurations; no compiler or launcher code."""
from pathlib import Path
import json,hashlib,shutil,re
B=Path('/home/dombarker/project-offloads/codex-cx-replay-dry-20261026')
T=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0')
g=json.loads((B/'RPy_graph.json').read_text()); manifest=[]
shutil.copyfile('/home/dombarker/project-offloads/codex-cx-s2w-20261023/S2W_run_host.py',B/'S2W_run_host.py')
(B/'lakefile.toml').write_text('name = "replaydry"\nversion = "0.1.0"\n')
(B/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for i,m in enumerate(g['order'][:400],1):
 assert m.startswith('Init.')
 rel=m.replace('.','/')+'.lean'; src=T/'src/lean'/rel; dst=B/rel
 dst.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(src,dst)
 imports=[]
 for line in src.read_text().splitlines():
  hit=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.*)',line)
  if hit:imports.extend(n for n in re.findall(r'[A-Za-z_][\w.]*',hit[1].split('--')[0]) if n != 'all')
 prior={r['module'] for r in manifest}
 assert all(n in prior for n in imports), (m,'not freshly built predecessor',imports)
 a=f'RPy_{i:03d}'
 row=dict(module=m,attempt=a,source=str(src),source_sha256=h(src),source_bytes=src.stat().st_size,imports=imports,object=m.replace('.','/')+'.olean')
 manifest.append(row)
 cfg=dict(kind='lean',env={'LEAN_PATH':str(B)},timeout=540,command=[str(T/'bin/lake'),'env','lean','-j1','-M7000','-DElab.async=false','-o',row['object'],rel],sources=[rel],attempt=a,source_revision='7d1ea416bd4c185e63c278623727adc4f3c9c483',source_tree_dirty=False,deps_fingerprint={'scope':'fresh Init dependency-order replay; direct object hashes pinned immediately before launch','bootstrap_lean_sha256':h(T/'bin/lean'),'toolchain':'leanprover/lean4:v4.32.0'},expected_time='source elaboration and kernel checking of one Init module')
 (B/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
(B/'RPy_source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('prepared',len(manifest),'source-only copies; no cached research objects')
