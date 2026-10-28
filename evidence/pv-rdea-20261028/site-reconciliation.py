from pathlib import Path
import json,re,hashlib,subprocess
D=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028')
R=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust')
rows=[]
for row in json.loads((D/'mir-candidates.json').read_text()):
 i=row['id'];sites=[]
 for h in row['hits']:
  m=re.search(r' at (.*?):(\d+):(\d+):',h['text'])
  if not m:continue
  p=Path(m[1]);line=int(m[2])
  if not p.is_absolute():p=D.parent/'codex-pv-fscan-20261028/src/tools/r1-cost-probe'/p
  if not p.exists():p=R/p
  excerpt=None;sha=None
  if p.exists():
   raw=p.read_bytes();ls=raw.decode().splitlines();excerpt=ls[max(0,line-5):line+5];sha=hashlib.sha256(raw).hexdigest()
  sites.append(dict(**h,source=str(p),source_line=line,source_sha256=sha,argument_source_excerpt=excerpt))
 role=('application endpoint' if i in [2,17] else 'runtime candidate; not linked out of line; inlining/dispatch exclusion still requires closure' if i in [0,1,19,20,21,22] else 'build/proc-macro only; no runtime invocation from spend entry points')
 rows.append(dict(id=i,function=row['function'],mir=row['mir'],body_sha256=row['body_sha256'],classification=role,sites=sites))
std=json.loads((D/'stdlib-inlined-sites-v2.json').read_text())
for x in std['sites']:
 o=x['source_origin'];p=R/o['file'];line=o['line'];raw=p.read_bytes();ls=raw.decode().splitlines()
 x.update(source=str(p),source_sha256=hashlib.sha256(raw).hexdigest(),argument_source_excerpt=ls[max(0,line-5):line+5])
(D/'site-reconciliation.json').write_text(json.dumps(dict(binary=json.loads((D/'client-artifact.json').read_text()),MIR_candidates=rows,stdlib=std,complete=False,remaining='Indirect dispatch closure and source-to-inlined-code completeness are not certified. Build-only exclusions are mechanical unit-graph classifications, not mere absence of an nm symbol.'),indent=2)+'\n')
print('MIR candidate functions',len(rows),'source sites',sum(len(x['sites']) for x in rows),'std inline sites',len(std['sites']))
