#!/usr/bin/env python3
"""Read-only collector for the R427 proc-macro2 cache miss diagnosis."""
import hashlib,json,pathlib
ROOTS={
 'parent':pathlib.Path('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/charon/target'),
 'candidate':pathlib.Path('/home/dombarker/project-offloads/aspis-r427-raw-mir-observer-20261002-a/charon/target'),
}
CARGO=pathlib.Path('/home/dombarker/.cargo')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def record(p,base):
 d={'path':str(p.relative_to(base)),'bytes':p.stat().st_size,'sha256':sha(p),'mtime_ns':p.stat().st_mtime_ns}
 if p.suffix=='.json':
  try:d['json']=json.loads(p.read_text())
  except Exception as e:d['parse_error']=str(e)
 return d
out={'classification':'read-only metadata query after R427 build attempt stopped before compiling proc-macro2','roots':{},'cargo_registry':{},'configs':[]}
for label,root in ROOTS.items():
 rows=[]
 for pattern in ('release/.fingerprint/proc-macro2-*/*','release/deps/*proc_macro2*','release/build/proc-macro2-*/*','release/.fingerprint/charon-*/bin-charon-driver.json'):
  for p in sorted(root.glob(pattern)):
   if p.is_file():
    x=record(p,root)
    if p.suffix=='.d':x['first_1200_text']=p.read_text(errors='replace')[:1200]
    rows.append(x)
 out['roots'][label]={'root':str(root),'artifacts':rows}
for p in [CARGO/'registry/src/index.crates.io-1949cf8c6b5b557f/proc-macro2-1.0.96/Cargo.toml',CARGO/'registry/cache/index.crates.io-1949cf8c6b5b557f/proc-macro2-1.0.96.crate']:
 if p.is_file():out['cargo_registry'][str(p)]={'bytes':p.stat().st_size,'sha256':sha(p),'mtime_ns':p.stat().st_mtime_ns}
for p in [CARGO/'config.toml',CARGO/'config',pathlib.Path('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/.cargo/config.toml'),pathlib.Path('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/.cargo/config'),pathlib.Path('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/charon/.cargo/config.toml'),pathlib.Path('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/charon/.cargo/config')]:
 if p.is_file():out['configs'].append({'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p),'text':p.read_text(errors='replace')})
print(json.dumps(out,indent=2,sort_keys=True))
