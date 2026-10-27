from pathlib import Path
import hashlib,json,subprocess,shutil,os
B=Path(__file__).resolve().parent
subprocess.run(['python3',str(B/'XRh_inventory.py')],check=True)
O=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027');S=Path('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/src')
def artifact(p):return dict(path=str(p),sha256=hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),bytes=p.stat().st_size)
pins=json.loads((O/'XRa_release_sourcepins.json').read_text());changed=[]
for r in pins['files']:
 p=S/r['path']
 if not p.is_file() or artifact(p)['sha256']!=r['sha256']:changed.append(r['path'])
newchanges=[]
for r in json.loads((B/'XRh_new_sourcepins.json').read_text()):
 for f in r['files']:
  p=B/r['name']/f['path']
  if artifact(p)['sha256']!=f['sha256']:newchanges.append(str(p))
base=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
runner=artifact(base/'S2W_run_host.py');ownrunner=artifact(B/'XRh_run_host.py');assert runner['sha256']==ownrunner['sha256']
row=dict(pinned_input=artifact(Path('/home/dombarker/project-offloads/codex-cx-extraction-repro7-20261027/XRg_07_release_candidate_tx1.llbc')),release_revision=pins['source_revision'],release_files_checked=len(pins['files']),changed_release_files=changed,changed_new_tool_sources=newchanges,runner=runner,own_runner=ownrunner,main_launcher=artifact(base/'S2W_lean_host.py'),artifacts=[artifact(p) for p in sorted(B.glob('XRh_*.llbc'))],outputs=[artifact(p) for p in sorted(B.glob('XRh_*generated*/*/*')) if p.is_file()],rustc_version=subprocess.check_output(['/home/dombarker/.cargo/bin/rustup','run','nightly-2026-09-17','rustc','-vV'],text=True),rustup_default=subprocess.check_output(['/home/dombarker/.cargo/bin/rustup','default'],text=True),backend_lean=(B/'XRh_new_aeneas/backends/lean/lean-toolchain').read_text(),backend_lakefile=artifact(B/'XRh_new_aeneas/backends/lean/lakefile.lean'),backend_manifest=artifact(B/'XRh_new_aeneas/backends/lean/lake-manifest.json'),print_axioms='N/A: no new Lean theorem or elaboration; generated files are unverified extraction artifacts')
row['new_source_diffs']={n:subprocess.check_output(['git','diff','--name-only'],cwd=B/n,text=True) for n in ['XRh_new_aeneas','XRh_new_charon']}
# Preserve only named executable outputs, then remove this job's rebuildable caches.
D=B/'XRh_bin';D.mkdir(exist_ok=True);bins=[]
for n,p in [('aeneas',B/'XRh_new_aeneas/src/_build/default/main.exe'),('charon',B/'XRh_charon_target/release/charon'),('charon-driver',B/'XRh_charon_target/release/charon-driver')]:
 q=D/n;shutil.copy2(p,q);assert artifact(p)['sha256']==artifact(q)['sha256'];bins.append(dict(**artifact(q),ldd=subprocess.run(['ldd',str(q)],capture_output=True,text=True).stdout))
row['preserved_binaries']=bins
cleanup=[]
for n in ['XRh_charon_target','XRh_release_target','XRh_opam','XRh_new_charon/_build','XRh_new_aeneas/src/_build','XRh_new_aeneas/_build']:
 p=B/n
 if p.exists():shutil.rmtree(p);cleanup.append(n)
row['removed_own_rebuildable_caches']=cleanup
assert not changed and not newchanges
(B/'XRh_HostAudit.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps({k:row[k] for k in ['release_files_checked','changed_release_files','changed_new_tool_sources','removed_own_rebuildable_caches']}),flush=True)
