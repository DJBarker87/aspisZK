from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-field4-20261108';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
paths=[B+'/NKJ_objects',B+'/NKJ_seed/NKH',B+'/NKJ_seed/NGH']+json.loads((E.parent/'ledger18-20261108/NKH_PATHS.json').read_text())
a,target=sys.argv[1:];name=target.replace('.','/')+'.lean'
cfg=dict(attempt=a,kind='lean',module=target,sources=[name],upload=[name],command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o','NKJ_objects/'+target.replace('.','/')+'.olean',name],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NKJ_tmp',LEAN_PATH=':'.join(paths)),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time='focused emitted/reference lemma elaboration; no package replay')
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2))
