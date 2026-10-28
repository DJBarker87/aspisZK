"""Run unchanged NCZ at explicit immutable snapshots; retain frontier deltas."""
from pathlib import Path
import json,importlib.util,subprocess,hashlib,collections,sys
E=Path(__file__).resolve().parent;R=E.parents[1]
spec=importlib.util.spec_from_file_location('ncz',R/'evidence/native-compledger-20261028/NCZ_validate.py');n=importlib.util.module_from_spec(spec);spec.loader.exec_module(n)
SNAPSHOT='285e784742' # initial merged research snapshot, before this audit's reports
SNAPSHOT=subprocess.check_output(['git','rev-parse',SNAPSHOT],text=True,cwd=R).strip()
original_git=n.git
base=n.BASE
def at(rev):
 n.BASE=rev
 def pinned_git(*args):return original_git(*(rev if a=='HEAD' else a for a in args))
 n.git=pinned_git
# Archived baseline adapter: read immutable Git bytes, since later merged
# reports legitimately differ in the present worktree. No baseline check is waived.
oldread=n.Store.read
def archived_read(self,p,cite=True):
 assert p in self.tree and self.head_tree.get(p)==self.tree[p][0],p
 if p not in self.cache:self.cache[p]=self.blob(self.tree[p][0])
 b=self.cache[p]
 if cite:self.used[p]={'sha256':n.sha(b),'bytes':len(b),'git_blob':self.tree[p][0],'revision':n.BASE}
 return b
n.Store.read=archived_read
at(base)
before=n.collect();n.validate_invariants(before)
existing=json.loads((R/'evidence/native-compledger-20261028/NCZ_LEDGER.json').read_text())
assert existing==before,'archived NCZ snapshot mismatch'
n.Store.read=oldread
at(SNAPSHOT)
after=n.collect();n.validate_invariants(after)
(E/'NDJ_NCZ_SNAPSHOT.json').write_text(n.dump(after))
deltas={p:json.loads((R/p).read_text()) for p in ['evidence/native-front3-20261028/NDF_LEDGER_DELTA.json','evidence/native-front4-20261028/NDG_LEDGER_DELTA.json']}
# No semantic adoption inferred: a delta is separate, qualified local support.
coverage=dict(baseline_revision=base,snapshot_revision=SNAPSHOT,baseline_validation='NCZ collect and validate_invariants, exact equality',snapshot_validation='NCZ collect and validate_invariants',baseline_coverage=before['coverage'],refreshed_index_coverage=after['coverage'],deltas=deltas,delta_policy='Separate qualified local packets, not unconditional/native caller or composed closure; no automatic promotion into the NCZ selected claim index',composed_closed=0)
(E/'NDJ_COVERAGE.json').write_text(n.dump(coverage))
print(n.dump({k:v for k,v in coverage.items() if k!='deltas'}))
