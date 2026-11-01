"""Read-only recovery audit before allocating any new IDs."""
from pathlib import Path
import subprocess,json,hashlib
D=Path('evidence/pv-b3p6-20261028/resume17');inv=json.loads((D/'D540-final-host-inventory.json').read_text())
code='''from pathlib import Path
import json,hashlib,subprocess,time
H=Path('/home/dombarker/project-offloads/codex-pv-b3p6-20261028');R=H/'resume17'
expected=EXPECTED
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mismatches=[]
for n,h in expected.items():
 p=H/n
 if not p.exists() or sha(p)!=h:mismatches.append(dict(path=n,expected=h,actual=sha(p)if p.exists()else None))
receipts=[]
for pattern in ['lean-738*/receipt/receipt.json','resume17/N739*/receipt/receipt.json','resume17/K739*/receipt/receipt.json','resume17/S739*/receipt/receipt.json']:
 for p in H.glob(pattern):receipts.append(dict(path=str(p.relative_to(H)),sha256=sha(p),exit_status=json.loads(p.read_text())['exit_status']))
t=json.loads((H/'TALLY-resume17.json').read_text());quiet=Path('/home/dombarker/project-offloads/QUIET_WINDOW.json');now=time.time()
q=json.loads(quiet.read_text())if quiet.exists()else None
print(json.dumps(dict(epoch=now,compared_host_artifacts=len(expected),mismatches=mismatches,tally=t,receipts=receipts,live_scopes=subprocess.check_output(['systemctl','--user','list-units','pv-b3p6-*','--no-pager'],text=True),quiet_marker=q,quiet_in_force=bool(q and now<q['until']),mutation_performed=False),indent=2))
'''.replace('EXPECTED',repr(inv['hashes']))
x=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True))
assert not x['mismatches'],x['mismatches'];assert '0 loaded units listed' in x['live_scopes'],x['live_scopes']
counts={k:sum(v['path'].startswith(prefix)for v in x['receipts'])for k,prefix in [('lean','lean-'),('extraction','resume17/N'),('kani','resume17/K'),('std','resume17/S')]}
assert counts==dict(lean=33,extraction=20,kani=18,std=6),counts
assert x['tally']['lean_attempts']==33 and len(x['tally']['used_ids'])==34
x.update(branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip(),entry_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),worktree=str(Path.cwd()),charged=counts,remaining=dict(lean=7,extraction=10,kani=12,std=0),next_unused=dict(lean=73832,extraction='N73927',kani='K73949',audit=[73899]),retired=['K73944'],notes=['No orphan or uncollected receipt; every D537 host hash matches.','K73949/K73950 prepared sum controls are unrun; do not reuse them for a different harness.','Only 11 high consecutive Kani IDs remain; a twelfth run requires reconciling a lower untouched hole, never extending the range.','Inherited r1p-common.txt and prompt-pv-b3p6f.txt are absent at their historical paths; no missing instruction invented.'])
(D/'RECOVERY-D542.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps({k:x[k]for k in ['compared_host_artifacts','mismatches','charged','remaining','next_unused','quiet_in_force']}))
