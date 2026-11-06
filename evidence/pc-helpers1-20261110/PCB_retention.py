from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
names=['PCB_HANDOFF.md','PCB_CLOSED.json','PCB_CANDIDATES.json','PCB_CALLER_CLAUSES.json','PCB_LEDGER_DELTA.json','PCB_AUDIT.json','PCB_AUDIT_ACCEPTED_STAGE6.json','PCB_AUDIT_LATEST.json','PCB_AUDIT_ROOTS.json','PCB_COMBINED_IMPORT.lean','PCB_ACCEPTED_COMBINED_IMPORT.lean.txt','PCB_REMAINING.md','PCB_REMAINING.json','PCB_REACH.md','PCB_REACH.json','PCB_BUDGET.json','PCB_RELEASE_PINS.json','PCB_CERTIFICATES.md','PCB_STUBS.md','PCB_FAILING_STEP.md','PCB_FINAL_HARNESS.patch','PCB_FINAL_HARNESS.patch.sha256','PCB_PATCH_CHECK.json','PCB_BODY_CHECKS.json','PCB_POST_LOOP_CHECKS.json','PCB_BOUNDARY_CORRESPONDENCE.json']
files={n:(E/n).read_text() for n in names}
code=f'''from pathlib import Path
import json,hashlib,shutil
b=Path('/home/dombarker/project-offloads/codex-pc-helpers1-20261110');x=Path('/home/dombarker/project-offloads/codex-pc-helpers1-cache-20261110/PCB_exports_20261110');files=json.loads({json.dumps(files)!r});rows=[]
for n,s in files.items():
 p=x/'PCB_handoff'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s);rows.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
before=shutil.disk_usage(b)._asdict();removed=[]
for n in ['PCB_target','PCB_ref_target','PCB_tmp']:
 p=b/n
 if p.exists():
  assert p.parent==b and not p.is_symlink() and p.resolve().parent==b
  shutil.rmtree(p);removed.append(str(p))
after=shutil.disk_usage(b)._asdict();result=dict(metadata_copies=rows,removed_build_only=removed,before=before,after=after,retained_cache=str(x.parent),retained_objects=str(b/'PCB_objects'),retained_source=str(b/'PCB_src'),keys_created=False,transactions_created=False)
(x/'PCB_RETENTION.json').write_text(json.dumps(result,indent=1)+'\\n');print(json.dumps(result))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
(E/'PCB_RETENTION.json').write_text(json.dumps(json.loads(r.stdout),indent=1)+'\n');print('Retained copied cache/objects/source; removed only own Rust targets and temporary build directory')
