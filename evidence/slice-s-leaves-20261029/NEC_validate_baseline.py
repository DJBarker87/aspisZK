"""Run the unchanged NDT audit against its immutable snapshot, with the real sparse index.
This validates the baseline ledger copy only. It does not admit NEC proposals or
silently refresh the current-head report corpus.
"""
from pathlib import Path
import subprocess,json,os,tempfile,hashlib,time
E=Path(__file__).resolve().parent;R=E.parent.parent
base='f4ff4b340c06640d911632d110d49aa92e68e50e'
def git(*a):return subprocess.check_output(['git',*a],cwd=R,text=True).strip()
common=Path(git('rev-parse','--git-common-dir')).resolve()
index=Path(git('rev-parse','--git-path','index')).resolve()
assert index.is_file()
# Preserve the actual sparse-index deletion gate; no empty replacement index.
env=dict(os.environ,GIT_INDEX_FILE=str(index),GIT_WORK_TREE=str(R))
with tempfile.TemporaryDirectory(prefix='NEC-ndt-view-',dir=E) as temp:
 d=Path(temp);(d/'objects/info').mkdir(parents=True);(d/'refs').mkdir()
 (d/'HEAD').write_text(base+'\n')
 (d/'objects/info/alternates').write_text(str(common/'objects')+'\n')
 (d/'config').write_text('[core]\nrepositoryformatversion=0\nbare=false\n')
 env['GIT_DIR']=str(d)
 command=['python3',str(R/'evidence/native-ledger3-20261029/NDT_validate.py'),'--ledger',str(E/'NEC_LEDGER_COPY.json')]
 start=time.monotonic();run=subprocess.run(command,cwd=R,env=env,capture_output=True,text=True)
 (E/'NEC_BASELINE_PINNED_VALIDATION.json').write_text(run.stdout)
 (E/'NEC_BASELINE_PINNED_VALIDATION.stderr').write_text(run.stderr)
 receipt=dict(command=command,scope='immutable authoritative baseline only; NEC proposals NOT admitted',git_head=base,current_branch_head=git('rev-parse','HEAD'),uses_real_sparse_index=True,index_sha256=hashlib.sha256(index.read_bytes()).hexdigest(),exit_status=run.returncode,wall_seconds=time.monotonic()-start,ledger_sha256=hashlib.sha256((E/'NEC_LEDGER_COPY.json').read_bytes()).hexdigest(),validator_sha256=hashlib.sha256((R/'evidence/native-ledger3-20261029/NDT_validate.py').read_bytes()).hexdigest())
 (E/'NEC_BASELINE_PINNED_RECEIPT.json').write_text(json.dumps(receipt,indent=1)+'\n')
 print(json.dumps(receipt));print(run.stderr[-1500:]);raise SystemExit(run.returncode)
