#!/usr/bin/env python3
import pathlib,json,subprocess,hashlib
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026';a=[json.loads(x) for x in (e/'resume8-attempts.jsonl').read_text().splitlines()]
expected={r['module']+'.olean':r['object_sha256'] for r in a if r['accepted']}
code='''import pathlib,hashlib,json,subprocess,shutil
j=pathlib.Path('/home/dombarker/project-offloads/codex-pv-srcid-20261026');shared=pathlib.Path('/home/dombarker/project-offloads/aspis-joint-20261019/objects');expected=EXPECTED
scopes={}
for name in ['srcid8-prefix900','srcid8-prefix01-try1']:
 p=subprocess.run(['systemctl','--user','show','pv-'+name+'.scope','-p','ActiveState','-p','SubState'],capture_output=True,text=True)
 scopes[name]=p.stdout;assert 'ActiveState=inactive' in p.stdout
objects=[];cache=j/'lean-objects'
if cache.exists():
 for p in cache.rglob('*'):
  if not p.is_file():continue
  rel=str(p.relative_to(cache));assert p.suffix=='.olean' and rel in expected,rel
  sha=hashlib.sha256(p.read_bytes()).hexdigest();same=hashlib.sha256((shared/rel).read_bytes()).hexdigest()
  assert sha==same==expected[rel],rel
  objects.append(dict(path=rel,sha256=sha,bytes=p.stat().st_size))
 manifests={}
 for rel in ['Cargo.toml','Cargo.lock','rust-toolchain.toml','.cargo/config.toml']:
  p=j/'repo'/rel
  if p.is_file():manifests[rel]=hashlib.sha256(p.read_bytes()).hexdigest()
 cargo=j/'kani-target';cargo_files=[p for p in cargo.rglob('*') if p.is_file()] if cargo.exists() else []
 cargo_bytes=sum(p.stat().st_size for p in cargo_files)
 if cache.exists():shutil.rmtree(cache)
 if cargo.exists():shutil.rmtree(cargo)
 print(json.dumps(dict(scopes=scopes,objects=objects,removed_lean_cache_bytes=sum(p['bytes'] for p in objects),removed_cargo_cache_bytes=cargo_bytes,removed_cargo_cache_files=len(cargo_files),postrun_repo_manifests=manifests,source_snapshots_and_preimages_retained=True,shared_sources_and_objects_retained=True,tmp_solver_cleanup='No exact owned /tmp solver path was identified after scope termination; unrelated temporaries were not removed.',wallet_or_account_keys_created_or_touched=False)))
'''.replace('EXPECTED',repr(expected))
p=subprocess.run(['ssh','-o','ConnectTimeout=10','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True,check=True);r=json.loads(p.stdout)
for rel,sha in r['postrun_repo_manifests'].items():
 b=subprocess.run(['git','show','HEAD:'+rel],cwd=root,capture_output=True);r.setdefault('postrun_manifest_commit_matches',{})[rel]=b.returncode==0 and hashlib.sha256(b.stdout).hexdigest()==sha
(e/'resume8-cache-cleanup.json').write_text(json.dumps(r,indent=2)+'\n');print('Removed own Lean object cache:',len(r['objects']),'files;',r['removed_lean_cache_bytes'],'bytes; own Cargo cache:',r['removed_cargo_cache_bytes'],'bytes; postrun manifest matches',r['postrun_manifest_commit_matches'])
