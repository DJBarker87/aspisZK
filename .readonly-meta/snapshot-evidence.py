#!/usr/bin/env python3
"""Read/hash-only snapshot after focused native/extraction/Lean checks."""
from pathlib import Path
import hashlib,json,shutil,tarfile,tomllib
W=Path('/home/dombarker/project-offloads/aspis-r1-readonly-meta-20261016');E=W/'extraction';P=W/'proofs';O=W/'evidence-stage';O.mkdir(exist_ok=False)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def put(p,rel):
 q=O/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
 return {'member':rel,'source_path':str(p),'sha256':sha(q),'bytes':q.stat().st_size}
def dump(rel,x):
 q=O/rel;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(x,indent=2)+'\n')
for n in ['run-host.py','inputs.json','inputs-original.json','setup.json']:
 put(W/n,'native/'+n)
for p in sorted((W/'runs').rglob('*')):
 if p.is_file():put(p,'native/'+str(p.relative_to(W)))
inputs=json.loads((W/'inputs.json').read_text())
for rel,digest in inputs['files'].items():
 assert sha(W/rel)==digest;put(W/rel,'native/'+rel)
for n in ['run-host.py','Cargo.lock.seed','audit-dependencies.py','dependency-audit.json','tool-pins.json','ReadonlyMeta.llbc']:
 put(E/n,'extraction/'+n)
for folder in ['input','runs','generated']:
 for p in sorted((E/folder).rglob('*')):
  if p.is_file():put(p,'extraction/'+str(p.relative_to(E)))
for n in ['runner.py']:
 put(P/n,'proofs/'+n)
for folder in ['sources','successful-targets','objects','runs']:
 for p in sorted((P/folder).rglob('*')):
  # The per-run overlay is a journalled symbolic-link namespace, not copied cache.
  if p.is_symlink():continue
  if p.is_file():put(p,'proofs/'+str(p.relative_to(P)))
# Retain every selected registry archive plus the real SDK reexport source crates.
dep=json.loads((E/'dependency-audit.json').read_text());seed=tomllib.loads((E/'Cargo.lock.seed').read_text())['package']
reg=Path('/home/dombarker/.cargo/registry');ix='index.crates.io-1949cf8c6b5b557f'
crates={r['name']+'-'+r['version']:r for r in dep['packages']}
for n,v in [('solana-program','2.3.0'),('solana-account-info','2.3.0'),('solana-program-entrypoint','2.3.0')]:
 r=next(r for r in seed if r['name']==n and r['version']==v);k=n+'-'+v
 crates[k]={**r,'archive':str(reg/'cache'/ix/(k+'.crate'))}
cp=[];source_audit=[]
selected={r['name']+'-'+r['version'] for r in dep['packages']}
for k,r in sorted(crates.items()):
 p=Path(r['archive']);assert sha(p)==r['checksum']
 cp.append({**put(p,'registry-archives/'+p.name),'name':r['name'],'version':r['version'],'checksum':r['checksum'],'selected':k in selected})
 if k in selected:
  files={}
  with tarfile.open(p) as t:
   for m in t.getmembers():
    if not m.isfile():continue
    rel=str(Path(m.name).relative_to(k));b=t.extractfile(m).read();actual=reg/'src'/ix/k/rel
    digest=hashlib.sha256(b).hexdigest();assert sha(actual)==digest
    files[rel]={'sha256':digest,'bytes':len(b)}
  source_audit.append({'name':r['name'],'version':r['version'],'archive_sha256':r['checksum'],'files':files})
dump('registry-archives.json',cp);dump('registry-source-file-audit.json',source_audit)
llbc=json.loads((E/'ReadonlyMeta.llbc').read_text());t=llbc['translated'];sourcefiles=[]
rust=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust')
for row in t['files']:
 s=row['name']['Local']
 if s=='lib.rs':p=E/'input/lib.rs';rel='extraction/input/lib.rs'
 elif s.startswith('/cargo/'):
  p=Path('/home/dombarker/.cargo')/s.removeprefix('/cargo/');rel='source-files/registry/'+str(p.relative_to(reg/'src'/ix))
 elif s.startswith('/rustc/'):
  p=rust/s.removeprefix('/rustc/');rel='source-files/rust/'+s.removeprefix('/rustc/')
 else:raise AssertionError(s)
 sourcefiles.append({**put(p,rel),'llbc_file_id':row['id'],'llbc_path':s})
for key,path in [('solana-program-2.3.0','src/lib.rs'),('solana-program-2.3.0','src/program_error.rs'),('solana-program-2.3.0','Cargo.toml'),('solana-program-entrypoint-2.3.0','src/lib.rs'),('solana-account-info-2.3.0','src/lib.rs')]:
 sourcefiles.append(put(reg/'src'/ix/key/path,'source-files/registry/'+key+'/'+path))
dump('source-files.json',sourcefiles)
def name(parts):return '::'.join(p['Ident'][0] if 'Ident' in p else '<impl:'+str(p['Impl'])+'>' for p in parts)
decls=[]
for section in ['type_decls','fun_decls','global_decls','trait_decls','trait_impls']:
 for row in t[section]:
  if row is None:continue
  m=row['item_meta'];s=row.get('body',row.get('kind'))
  decls.append({'section':section,'id':row['def_id'],'name':name(m['name']),'raw_name':m['name'],'opacity':m['opacity'],'opaque':s=='Opaque','span':m['span'],'shape':next(iter(s)) if isinstance(s,dict) else s})
errors=[]
def walk(x,path):
 if isinstance(x,dict):
  for k,v in x.items():
   if k=='Error':errors.append({'json_path':path+[k],'value':v})
   walk(v,path+[k])
 elif isinstance(x,list):
  for i,v in enumerate(x):walk(v,path+[i])
walk(t,['translated'])
dump('llbc-inventory.json',{'llbc_sha256':sha(E/'ReadonlyMeta.llbc'),'charon_version':llbc['charon_version'],'has_errors':llbc['has_errors'],'declarations':decls,'opaque_or_foreign':[x for x in decls if x['opaque'] or x['opacity']!='Transparent'],'error_nodes':errors,'generated_files':[str(p.relative_to(E/'generated')) for p in sorted((E/'generated').rglob('*')) if p.is_file()],'scope':'Foreign/opaque standard-library operations are resolved through the pinned Aeneas backend. All actual function/proof audit cones are standard-only; no external template or fabricated SDK replacement.'})
tools=json.loads((E/'tool-pins.json').read_text());paths={}
for r in tools['tools'].values():paths[r['path']]=r['sha256']
paths.update(tools['rust_runtime_binaries'])
paths.update({p:r['sha256'] for p,r in tools['host_dynamic_libraries'].items()})
for p,h in paths.items():assert sha(Path(p))==h
# Exact Lean runtime and all consumed imported files were verified by each run's snapshot preflight.
dump('final-runtime-recheck.json',{'tool_pins_sha256':sha(E/'tool-pins.json'),'verified_files':paths,'all_match':True})
put(W/'snapshot-evidence.py','snapshot-evidence.py')
print(json.dumps({'members':sum(p.is_file() for p in O.rglob('*')),'registry_archives':len(cp),'source_files':sum(len(r['files']) for r in source_audit),'opaque_or_foreign':sum(x['opaque'] or x['opacity']!='Transparent' for x in decls),'errors':errors}))
with tarfile.open(W/'readonly-meta-host-snapshot.tar.gz','w:gz') as tar:
 for p in sorted(O.rglob('*')):
  if p.is_file():tar.add(p,arcname=str(p.relative_to(O)),recursive=False)
print('ARCHIVE',sha(W/'readonly-meta-host-snapshot.tar.gz'))
