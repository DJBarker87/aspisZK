"""Read the live sibling branch before starting a callback; never touches its worktree."""
import json,subprocess,sys,datetime
from pathlib import Path
root=Path(__file__).resolve().parents[2]
branch='codex/pv-cb-20261026';n=int(sys.argv[1])
def git(*args):return subprocess.run(['git',*args],cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
log=git('log','-1',branch)
grep=git('grep','-n',f'op{n}_source',branch,'--','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CB_*.lean')
assert log.returncode==0 and grep.returncode in (0,1)
r=dict(op=n,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),branch=branch,log=log.stdout,grep=grep.stdout,grep_exit=grep.returncode,status='SKIPPED(sibling)' if grep.stdout else 'STARTED')
p=root/'evidence/pv-cb3-20261026'/f'op{n}-sibling-check{("-"+sys.argv[2]) if len(sys.argv)>2 else ""}.json'
assert not p.exists();p.write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r))
