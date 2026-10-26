from pathlib import Path
p=Path('evidence/envj-rebuild-20261026/EJR_build_host.py');s=p.read_text().replace('import subprocess,json,hashlib,re,time,datetime,os,sys','import subprocess,json,hashlib,re,time,datetime,os,sys,shutil')
a=s.index('def deps(r):');b=s.index('for r in rows:',a)
s=s[:a]+'''def deps(r):
 out=[]
 for m in r['imports']:
  own=r['workspace']+':'+m
  blocked=own in selected_keys and own not in succeeded
  p=None
  if not blocked:
   if '/' in m:
    first=next((p for p in dep_paths(r) if (p/m.split('/')[0]).is_dir()),None)
    if first is not None and (first/(m+'.olean')).is_file():p=first/(m+'.olean')
   else:p=next((p/(m+'.olean') for p in dep_paths(r) if (p/(m+'.olean')).is_file()),None)
  out.append(dict(module=m,path=str(p) if p else None,sha256=sha(p) if p else None))
 return out

def mirror_namespaces():
 # Lean selects a namespace directory as a unit. Provide complete fallback
 # views using symlinks, preserving concrete files compiled in each workspace.
 for ws,root in roots.items():
  target=root/'objects'
  for prefix in sorted({r['module'].split('/')[0] for r in rows if r['workspace']==ws and '/' in r['module']}):
   seen=set()
   for base in paths:
    if base==target:continue
    d=base/prefix
    if not d.is_dir():continue
    for src in sorted(d.rglob('*')):
     if not src.is_file() or not any(str(src).endswith(e) for e in ['.olean','.olean.private','.olean.server','.ir']):continue
     rel=src.relative_to(base)
     if rel in seen:continue
     try:canonical=src.resolve(strict=True)
     except (RuntimeError,OSError):continue
     dest=target/rel
     if canonical==dest:continue
     seen.add(rel)
     if dest.exists() and not dest.is_symlink():continue
     if dest.is_symlink():
      if dest.resolve()==canonical:continue
      dest.unlink()
     dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(canonical)

''' +s[b:]
s=s.replace("attempted={r['key'] for r in past};succeeded={r['key'] for r in past if r['exit']==0};attempt=30000+len(past)","""attempted={r['key'] for r in past};succeeded={r['key'] for r in past if r['exit']==0};attempt=30000+len(past)
selected_keys={r['key'] for r in rows}
reuses_file=T/'EJR_reuses.jsonl'
reuses=[json.loads(l) for l in reuses_file.read_text().splitlines()] if reuses_file.exists() else []
succeeded.update(r['key'] for r in reuses);attempted.update(r['key'] for r in reuses)
repair_keys={r['key'] for r in past if r['workspace']=='union' and r['exit']!=0 and any('object file' in e and 'does not exist' in e for e in r['errors'])}

def try_reuse(r,ds):
 fingerprint=lambda dd:[(d['module'].replace('.','/'),d['sha256']) for d in dd]
 for old in past:
  if old['exit'] or old['workspace'] not in roots or old['module']!=r['module'] or old['source_sha256']!=r['source_sha256'] or fingerprint(old['deps'])!=fingerprint(ds):continue
  source=roots[old['workspace']]/'objects'/(r['module']+'.olean')
  if not source.is_file() or sha(source)!=old['object_sha256']:continue
  dest=roots[r['workspace']]/'objects'/(r['module']+'.olean')
  source=source.resolve()
  if dest.exists() and not dest.is_symlink() and sha(dest)!=old['object_sha256']:raise RuntimeError('unexpected existing output '+str(dest))
  if dest.is_symlink():dest.unlink()
  dest.parent.mkdir(parents=True,exist_ok=True)
  if not dest.exists():dest.symlink_to(source)
  companions=[]
  for ext in ['.olean.private','.olean.server','.ir']:
   cp=source.with_suffix(ext) if ext=='.ir' else Path(str(source)+ext.removeprefix('.olean'))
   dp=dest.with_suffix(ext) if ext=='.ir' else Path(str(dest)+ext.removeprefix('.olean'))
   if cp.is_file():
    if dp.is_symlink():dp.unlink()
    if not dp.exists():dp.symlink_to(cp.resolve())
    companions.append(dict(path=str(dp),sha256=sha(dp)))
  record=dict(key=r['key'],module=r['module'],workspace=r['workspace'],source_sha256=r['source_sha256'],deps=ds,compiled_attempt=old['attempt'],object_sha256=sha(dest),object_bytes=dest.stat().st_size,source=str(source),target=str(dest),companions=companions,reason='same module/source and selected dependency object hashes; no compile rerun')
  with reuses_file.open('a') as f:f.write(json.dumps(record)+'\\n')
  reuses.append(record);succeeded.add(r['key']);attempted.add(r['key']);print('REUSED',r['key'],'from',old['attempt'],flush=True);return True
 return False""")
s=s.replace("pending=[r for r in rows if r['key'] not in attempted]", "pending=[r for r in rows if r['key'] not in attempted or r['key'] in repair_keys]")
s=s.replace("while pending and len(past)<budget:\n ready=[]", "while pending and len(past)<budget:\n mirror_namespaces()\n ready=[]")
s=s.replace("r,ds=ready[0];label='EJR-'+str(attempt);admission=admit(label);root=roots[r['workspace']];src=Path(r['host_path']);assert sha(src)==r['source_sha256'];obj=root/'objects'/(r['module']+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)", """r,ds=ready[0]
 if try_reuse(r,ds):
  pending.remove(r);save_state(pending,'building; identical objects reused');continue
 label='EJR-'+str(attempt);admission=admit(label);root=roots[r['workspace']];src=Path(r['host_path']);assert sha(src)==r['source_sha256'];obj=root/'objects'/(r['module']+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 if obj.is_symlink():obj.unlink()
 elif obj.exists():raise RuntimeError('refuse overwriting existing regular object '+str(obj))""")
s=s.replace("axioms=[l for l in s.splitlines() if 'axioms' in l]\n if any('sorryAx'", "axioms=[l for l in s.splitlines() if 'axioms' in l]\n lean_exit=ec\n if any('sorryAx'")
s=s.replace("deps_fingerprint=fp,exit=ec,outer_exit=outer", "deps_fingerprint=fp,exit=ec,lean_exit=lean_exit,validation_exit=ec,outer_exit=outer")
p.write_text(s)
