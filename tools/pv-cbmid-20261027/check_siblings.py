"""Check actual Lean source-law declarations before each operation."""
from pathlib import Path
import subprocess,json,sys,datetime
op,label=sys.argv[1:];checks=[]
for branch in ['codex/pv-cb-20261026','codex/pv-cb3-20261026','codex/pv-cblib-20261027']:
 rev=subprocess.check_output(['git','rev-parse',branch],text=True).strip()
 r=subprocess.run(['git','grep','-n',f'op{op}_source',rev,'--','*.lean'],text=True,capture_output=True)
 assert r.returncode in [0,1]
 checks.append(dict(branch=branch,revision=rev,command=['git','grep','-n',f'op{op}_source',rev,'--','*.lean'],exit=r.returncode,matches=r.stdout))
skip=any(x['exit']==0 for x in checks)
Path(f'evidence/pv-cbmid-20261027/sibling-op{op}-{label}.json').write_text(json.dumps(dict(op=op,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),decision='SKIP(sibling)' if skip else 'continue',checks=checks,note='Search-pattern metadata matches are retained separately in SIBLING-RECHECK-2.json; this check searches the actual Lean law files.'),indent=2)+'\n')
print(op,'SKIP(sibling)' if skip else 'no sibling source law')
sys.exit(77 if skip else 0)
