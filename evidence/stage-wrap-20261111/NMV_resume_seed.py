from NMV_formal import *
nnc=json.loads((E.parent/'root0-weak-20261111'/'NNC_ENV.json').read_text())
own=json.loads((E/'NMV_ENV.json').read_text())
roots=[p for p in nnc['LEAN_PATH'].split(':') if p not in own['LEAN_PATH'].split(':')]
script='''from pathlib import Path
import json,hashlib,shutil
B=Path.cwd();x=json.loads((B/'NMV_resume_seed_config.json').read_text());out=[];different=[]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for root in x['roots']:
 for p in sorted(Path(root).rglob('*.olean')):
  rel=p.relative_to(root)
  existing=next((Path(r)/rel for r in x['existing'] if (Path(r)/rel).is_file()),None)
  if existing:
   if sha(existing)!=sha(p):different.append(dict(source=str(p),selected=str(existing),source_sha256=sha(p),selected_sha256=sha(existing)))
   continue
  dest=B/'NMV_seed'/'NNC'/rel;dest.parent.mkdir(parents=True,exist_ok=True)
  for suffix in ['', '.private','.server']:
   f=Path(str(p)+suffix)
   if not f.is_file():continue
   q=Path(str(dest)+suffix)
   if q.exists():assert sha(q)==sha(f),(q,f)
   else:shutil.copy2(f,q)
   out.append(dict(source=str(f),destination=str(q),sha256=sha(q),bytes=q.stat().st_size))
  for ext in ['.lean','.ir']:
   f=p.with_suffix(ext)
   if f.is_file():
    q=dest.with_suffix(ext)
    if q.exists():assert sha(q)==sha(f)
    else:shutil.copy2(f,q)
    out.append(dict(source=str(f),destination=str(q),sha256=sha(q),bytes=q.stat().st_size))
report=dict(files=out,different_existing=different,source_revision=x['revision'])
(B/'NMV_resume_seed_report.json').write_text(json.dumps(report,indent=1)+'\\n')
print(json.dumps(report))
'''
config=dict(roots=roots,existing=own['LEAN_PATH'].split(':'),revision=subprocess.check_output(['git','rev-parse','HEAD:evidence/root0-weak-20261111/NNC_WriteFree.lean'],text=True).strip())
r=run('NMV_L121','inspect','NNC_seed',['python3','NMV_resume_seed_host.py'],{'NMV_resume_seed_host.py':script,'NMV_resume_seed_config.json':json.dumps(config)})
assert r['exit_status']==0
raw=lzma.decompress((E/'NMV_L121'/'stdout.log.xz').read_bytes()).decode();report=json.loads(raw.strip())
(E/'NMV_NNC_SEED.json').write_text(json.dumps(report,indent=1)+'\n')
own['LEAN_PATH']=B+'/NMV_seed/NNC:'+own['LEAN_PATH'];(E/'NMV_ENV.json').write_text(json.dumps(own,indent=1)+'\n')
print(json.dumps(dict(files=len(report['files']),different=report['different_existing'])))
