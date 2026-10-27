from pathlib import Path
import hashlib,json,shutil
B=Path(__file__).resolve().parent
assert B.name=='codex-cx-extraction-repro1-20261027'
base=json.loads((B/'XRa_recovered_sources.json').read_text())
audit=json.loads((B/'XRa_historical_extended-tool-audit.json').read_text())
errors=[]
for row in base['files']:
 p=B/'XRa_toolchain'/row['path']
 if row['symlink'] is not None:
  if not p.is_symlink() or str(p.readlink())!=row['symlink']:errors.append(row['path'])
 else:
  want=audit['exact_changed_files'].get(row['path'].removeprefix('aeneas/'),row['sha256']) if row['path'].startswith('aeneas/') else row['sha256']
  if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=want:errors.append(row['path'])
release=json.loads((B/'XRa_release_sourcepins.json').read_text());S=Path('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/src')
release_errors=[]
for row in release['files']:
 p=S/row['path']
 if not p.is_file() or hashlib.file_digest(p.open('rb'),'sha256').hexdigest()!=row['sha256']:release_errors.append(row['path'])
raw=json.loads((B/'XRa_release_candidate_tx1.llbc').read_text())['translated']
name_rows=[x for x in raw['item_names'] if 'tx1' in json.dumps(x) and 'candidate' in json.dumps(x)]
fun_sample=next((x for x in raw['fun_decls'] if x is not None),{})
summary={'toolchain_source_entries_checked':len(base['files']),'toolchain_source_errors':errors,'release_source_files_checked':len(release['files']),'release_source_errors':release_errors,'release_nonempty_functions':len(raw['fun_decls']),'release_nonempty_types':len(raw['type_decls']),'root_name_entries':name_rows,'function_record_keys':list(fun_sample)}
assert not errors and not release_errors,summary
assert name_rows,summary
out=B/'XRa_bin';out.mkdir(exist_ok=False)
artifacts=[]
for src,name,want in [(B/'XRa_charon-target/release/charon','charon','daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'),(B/'XRa_charon-target/release/charon-driver','charon-driver','efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45'),(B/'XRa_toolchain/aeneas/src/_build/default/main.exe','aeneas-b59d5188-extended','c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958')]:
 p=out/name;shutil.copy2(src,p);h=hashlib.file_digest(p.open('rb'),'sha256').hexdigest();assert h==want
 artifacts.append({'path':str(p),'sha256':h,'bytes':p.stat().st_size})
for name in ['XRa_release_candidate_tx1.llbc','XRa_historical.llbc']:
 p=B/name;artifacts.append({'path':str(p),'sha256':hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),'bytes':p.stat().st_size})
removed=[]
for rel in ['XRa_charon-target','XRa_release_target','XRa_opam','XRa_native_libs','XRa_toolchain/charon/_build','XRa_toolchain/aeneas/src/_build','XRa_toolchain/aeneas/.git']:
 p=B/rel;assert p.resolve().is_relative_to(B) and not p.is_symlink()
 if p.exists():shutil.rmtree(p);removed.append(rel)
summary.update(retained_artifacts=artifacts,removed_task_caches=removed,tool_executions_in_this_job=0)
(B/'XRa_HostArtifacts.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary),flush=True)
