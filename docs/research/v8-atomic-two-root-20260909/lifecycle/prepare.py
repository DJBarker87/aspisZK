#!/usr/bin/env python3
"""A second task-owned copy preserves the entire measured predecessor."""
import pathlib,hashlib,json,subprocess,shutil,difflib
ROOT=pathlib.Path('/home/dombarker/project-offloads/aspis-v8-atomic-lifecycle-20260909')
PARENT=ROOT.parent/'aspis-v8-atomic-two-root-20260909'
OLD=ROOT.parent/'aspis-v8-performance-20260908.scS2Jz'
REL=pathlib.Path('docs/research/v8-atomic-two-root-20260909/lifecycle')
EXP=pathlib.Path('docs/research/v8-no-work-100-20260907/experiments')
assert not ROOT.exists()
subprocess.run(['python3',str(PARENT/REL.parent/'artifact_guard.py'),'check'],check=True)
subprocess.run(['bash',str(OLD/EXP/'check_terminal_query_sources.sh'),'terminal-stack'],check=True)
subprocess.run(['cp','-a','--reflink=auto',str(PARENT),str(ROOT)],check=True)
assert not (ROOT/'.git').exists()
# Reviewable selected-source overlay against the exact parent source manifest.
# Only source/manifest files enter this copy; no moving-main data or external cache.
record={'parent_head':'0180a774ea823d2f8762ec9409e000a7d7922b19','base':'4aaa61e679189b2cf76bfc25c2e3ff8d5c76341e','source_parent':str(PARENT),'selected_source':str(OLD),'overlays':[]}
patch=[]
for folder in ['crates','programs',str(EXP)]:
 for src in sorted((OLD/folder).rglob('*')):
  if not src.is_file() or 'target' in src.parts or src.suffix not in {'.rs','.toml','.lock'}:continue
  name=src.relative_to(OLD);dest=ROOT/name
  assert dest.exists(),name
  before=dest.read_bytes();after=src.read_bytes()
  if before==after:continue
  record['overlays'].append({'path':str(name),'before':hashlib.sha256(before).hexdigest(),'after':hashlib.sha256(after).hexdigest()})
  patch.extend(difflib.unified_diff(before.decode().splitlines(True),after.decode().splitlines(True),fromfile='a/'+str(name),tofile='b/'+str(name)))
  dest.write_bytes(after)
(ROOT/REL/'selected-source.patch').write_text(''.join(patch))
(ROOT/REL/'evidence/preparation.json').write_text(json.dumps(record,indent=2)+'\n')
subprocess.run(['bash',str(ROOT/EXP/'check_terminal_query_sources.sh'),'terminal-stack'],check=True)
# The original model/driver source is preserved; a task-only derived driver
# hands its successful cloned runtime to lifecycle cleanup after all rollback tests.
atomic=ROOT/REL.parent/'driver.rs'
s=atomic.read_text().replace('    fs::write(&args.evidence, serde_json::to_vec_pretty(&result)?)?;','    fs::write(&args.evidence, serde_json::to_vec_pretty(&result)?)?;\n    *svm = settled;')
(ROOT/REL/'atomic_driver.rs').write_text(s)
p=ROOT/'results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/src/main.rs'
s=p.read_text()
s=s.replace('../../../../docs/research/v8-atomic-two-root-20260909/driver.rs','../../../../docs/research/v8-atomic-two-root-20260909/lifecycle/atomic_driver.rs')
s='#[path="../../../../docs/research/v8-atomic-two-root-20260909/lifecycle/driver.rs"]\nmod lifecycle_run;\n'+s
s=s.replace('const PROOF_ACCOUNT_BYTES: [u8; 32] = [0x45; 32];','const PROOF_ACCOUNT_BYTES: [u8; 32] = [237,73,40,198,40,209,194,198,234,233,3,56,144,89,149,97,41,89,39,58,92,99,249,54,54,193,70,20,172,135,55,209];')
needle='    put_account(&mut svm, proof_key, verifier_program, proof_image)?;'
assert s.count(needle)==1
s=s.replace(needle,'    if env::var_os("ASPIS_LIFECYCLE").is_none(){\n        put_account(&mut svm, proof_key, verifier_program, proof_image.clone())?;\n    }')
needle='    if env::var_os("ASPIS_ATOMIC_EXPERIMENT").is_some() {\n        return atomic::run'
assert s.count(needle)==1
s=s.replace(needle,'    if env::var_os("ASPIS_LIFECYCLE").is_some(){\n        return lifecycle_run::run(&mut svm,&payer,&args,&protected_keys,instruction,&lane,&candidate_afterstate,&request,&proof_image);\n    }\n'+needle)
p.write_text(s)
# Reuse the identical dependency resolution; rename only this wrapper package.
lock=(ROOT/EXP/'complete-sbf/Cargo.lock').read_text().replace('name = "aspis-v8-complete-sbf"','name = "aspis-v8-lifecycle-sbf"')
(ROOT/REL/'verifier/Cargo.lock').write_text(lock)
print(json.dumps({'source_overlay_files':len(record['overlays']),'root':str(ROOT)}))
