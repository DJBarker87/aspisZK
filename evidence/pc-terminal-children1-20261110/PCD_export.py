"""Post-processing only: hash selected objects, copy own exports, no prover/build launch."""
from PCD_transport import *
import lzma,base64,hashlib
mods=[json.loads(l)['module'] for l in lzma.decompress((E/'PCD_LOADED_scan.jsonl.xz').read_bytes()).decode().splitlines()]
own=[x['module'] for x in json.loads((E/'PCD_CURRENT_SOURCE_CHECK.json').read_text())]+['PCD_COMBINED_IMPORT','PCD_ProofDriver']
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,shutil,os,base64
b=Path({B!r});cfg=json.loads((b/'PCD_L060.json').read_text());env=cfg['env'];roots=list(dict.fromkeys([str(Path(p)) for p in env['LEAN_PATH'].split(':') if p]+[env['LEAN_SYSROOT']+'/lib/lean']))
needed=set({mods!r});needed.update({own!r});found={{}}
for root in roots:
 d=Path(root)
 if not d.is_dir():continue
 for p in d.rglob('*.olean'):
  name=str(p.relative_to(d))[:-6].replace('/','.')
  if name in needed:
   found[name]=p;needed.remove(name)
 if not needed:break
assert not needed,sorted(needed)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
 return h.hexdigest()
records=[];export=b/'PCD_exports_20261110';export.mkdir(exist_ok=True);copied=[]
for name,p in sorted(found.items()):
 files=[]
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not z.is_file():continue
  before=z.stat();h=sha(z);after=z.stat();assert (before.st_size,before.st_mtime_ns)==(after.st_size,after.st_mtime_ns)
  files.append(dict(path=str(z),sha256=h,bytes=after.st_size))
  if name in {own!r}:
   rel=Path(name.replace('.','/'))
   suffix=str(z)[len(str(p)):] if str(z).startswith(str(p)) else '.ir'
   target=export/(str(rel)+('.olean'+suffix if suffix!='.ir' else '.ir'));target.parent.mkdir(parents=True,exist_ok=True)
   shutil.copy2(z,target);assert sha(target)==h and not os.path.samefile(z,target)
   copied.append(dict(module=name,source=str(z),export=str(target),sha256=h,hardlinked=False))
 records.append(dict(module=name,objects=files))
source_dir=export/'sources';source_dir.mkdir(exist_ok=True)
for name in {own!r}:
 source=b/'PCD_generated'/(name.replace('.','/')+'.lean')
 if source.is_file():
  out=source_dir/(name.replace('.','/')+'.lean');out.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source,out)
manifest=dict(status='PINNED',loaded_modules=len({mods!r}),all_modules_pinned=len(records),search_path=roots,objects=records,method='first matching object in actual final LEAN_PATH plus sysroot; sidecars included; no build/prover/audit binary launched')
(b/'PCD_IMPORT_OBJECTS.json').write_text(json.dumps(manifest,indent=1)+'\\n')
info=dict(export=str(export),copies=copied,baseline_objects='retained in already seeded/pinned directories; no second corpus copied',lean_path=[str(export)]+roots,source_revision=cfg['source_revision'])
(b/'PCD_EXPORT.json').write_text(json.dumps(info,indent=1)+'\\n')
print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode() for n in ['PCD_IMPORT_OBJECTS.json','PCD_EXPORT.json']}}))
''')
assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():
 raw=base64.b64decode(s)
 if n=='PCD_IMPORT_OBJECTS.json':
  (E/(n+'.xz')).write_bytes(lzma.compress(raw));(E/(n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n')
 else:(E/n).write_bytes(raw)
x=json.loads((E/'PCD_EXPORT.json').read_text());print('Pinned every loaded import and copied '+str(len(x['copies']))+' own object/sidecar exports without hardlinks; no additional scope.')
