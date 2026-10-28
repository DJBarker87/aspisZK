from pathlib import Path
import subprocess,json,hashlib,resource
D=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028')
rust='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc'
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
cmd=[rust,'--edition=2021','-Copt-level=3','-Cdebug-assertions=false','-Coverflow-checks=false','-Cpanic=unwind',str(D/'reachable-oom.rs'),'-o',str(D/'reachable-oom')]
subprocess.run(cmd,check=True)
results={}
for mode in ['native','old-reference']:
 p=subprocess.run([str(D/'reachable-oom'),mode],text=True,capture_output=True)
 results[mode]=dict(exit=p.returncode,stdout=p.stdout,stderr=p.stderr)
assert results['native']['exit']==-6,results
assert results['old-reference']['exit']==0,results
j=dict(classification='finite native validation with a deliberately failing diagnostic allocator; not a witness-dependent leak, production OOM measurement, or complete native refinement',command=cmd,toolchain=subprocess.check_output([rust,'-vV'],text=True),profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',features='std-only fixture; deployed project feature graph inherited from pv-rdb1 resolved-features.json, SHA256 613c405ef941cc940fd003ece28b23d910d327e02e19a9f7945bf2b939858f73',source_sha256=hashlib.sha256((D/'reachable-oom.rs').read_bytes()).hexdigest(),results=results)
(D/'reachable-oom.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j))
