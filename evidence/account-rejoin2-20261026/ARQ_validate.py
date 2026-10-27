"""Offline ARQ receipts, source identity, unchanged endpoint and atomic recount."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent; R=E.parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(name,x): (E/name).write_text(json.dumps(x,indent=2)+'\n')
def norm(s): return re.sub(r'\s+',' ',s).strip()
receipts=[]
for p in sorted(E.glob('ARQ_[0-9][0-9][0-9]/receipt.json')):
 x=json.loads(p.read_text()); receipts.append(x)
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert len(x['sources'])==1 and '-M7000' in x['command']
 assert int(x['swaps'])==0
 assert x['source_revision'] and x['deps_fingerprint']['selected_objects']
 for s in x['sources']: assert sha(p.parent/'sources'/s)==x['source_hashes'][s]
 if x['exit_status']==0:
  for line in x['print_axioms']:
   if 'does not depend on any axioms' in line: continue
   names=set(re.search(r'\[(.*)\]',line).group(1).split(', '))
   assert names <= {'propext','Classical.choice','Quot.sound'},line

assert len(receipts)==96
assert len({x['attempt'] for x in receipts})==96
manifest=json.loads((E/'ARQ_HOST_MANIFEST.json').read_text())
for p in (R/'lean').glob('ARQ_*.lean'):
 assert manifest[p.name]['sha256']==sha(p)
 assert any(x['exit_status']==0 and x['source_hashes'].get(p.name)==sha(p) for x in receipts)
 passed=next(x for x in receipts if x['exit_status']==0 and x['source_hashes'].get(p.name)==sha(p))
 for decl in re.findall(r'^#print axioms (\S+)',p.read_text(),re.M):
  assert any("'"+decl+"'" in line or "."+decl+"'" in line for line in passed['print_axioms']), (p.name,decl)
 assert not re.search(r'\b(sorry|admit|native_decide|maxHeartbeats|maxRecDepth)\b|^\s*axiom\s',re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S),re.M)
for n in ['Rc9_Top.lean']:
 assert manifest[n]['sha256']==sha(R/'lean'/n)
for before,after in [('ARQ_BEFORE_SOURCE.lean.txt','ARQ_AFTER_SOURCE.lean.txt'),('ARQ_BEFORE_KERNEL.lean.txt','ARQ_AFTER_KERNEL.lean.txt')]:
 assert norm((E/before).read_text())==norm((E/after).read_text())
assert sha(E/'ARQ_BEFORE_SOURCE.lean.txt')==sha(R/'lean/Rc9_Top.lean')
assert '⋯' not in (E/'ARQ_AFTER_KERNEL.lean.txt').read_text()
basefile=R/'evidence/recount9-20261026/Rc9_premises.json'; base=json.loads(basefile.read_text())
def tally(rs):
 return dict(rows=len(rs),classes={c:sum(r['classification']==c for r in rs) for c in ['T','P','G','C']},by_owner={o:{c:sum(r['classification']==c and r['owner']==o for r in rs) for c in ['T','P','G','C']} for o in ['lead','session A','external']})
def scopes(rs):
 return {s:tally([r for r in rs if r['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']}|{'deduplicated actual plus non-alias deployment':tally([r for r in rs if r['scope']!='deployment alias'])}
raw=scopes(base['rows']); distinct=scopes([r for r in base['rows'] if r['id']!='L137'])
assert raw==base['raw_counts'] and distinct==base['counts']
ledger=dict(actual_theorem='AspisR1.Rc9_Top.deployed',method=base['method'],baseline=str(basefile.relative_to(R)),baseline_sha256=sha(basefile),aliases=base['aliases'],rows=base['rows'],before=dict(raw=raw,distinct=distinct),after=dict(raw=raw,distinct=distinct),removed=[],added=[],reclassified=[],delta=dict(T=0,P=0,G=0,C=0),source_before_sha256=sha(E/'ARQ_BEFORE_SOURCE.lean.txt'),source_after_sha256=sha(E/'ARQ_AFTER_SOURCE.lean.txt'),kernel_before_sha256=sha(E/'ARQ_BEFORE_KERNEL.lean.txt'),kernel_after_sha256=sha(E/'ARQ_AFTER_KERNEL.lean.txt'),scope='Rc9 unchanged. Pointwise ARQ raw/recovery/coin/domination theorems are not an installed all-world replacement. WorldSupport is an unproved implementation target; no bundling discount. Native/global witnesses/guards retained.')
dump('ARQ_LEDGER_DELTA.json',ledger)
final=next(x for x in receipts if x['attempt']=='ARQ_095')
summary=dict(lean_attempts=len(receipts),passes=sum(x['exit_status']==0 for x in receipts),
 excluded=[x['attempt'] for x in receipts if x['exit_status']!=0],kani_runs=0,dependency_builds=0,
 total_lean_wall_seconds=sum(x['wall_seconds'] for x in receipts),
 peak_rss_kib=max(int(x['peak_rss_kib']) for x in receipts),swaps=0,budget_exhausted=False, remaining_lean_attempts=4, combined_final_audit_run=False, manifest_provenance="Offline retained passing snapshots; no fresh host inventory", kernel_statement_provenance="Inherited ARP full print; source unchanged; no fresh full kernel print",
 stop='Mandatory infrastructure stop: attempt 097 failed before compiler launch because the existing host reservation.py was missing. 96/100 actual Lean invocations. All-world native support, deployed representation and actual-top replacement remain open. JFr fixture existence pending; conditionally composed.',
 final_target=final['sources'][0],final_receipt={k:final[k] for k in ['attempt','source_revision','exit_status','wall_seconds','peak_rss_kib','swaps']},
 source_root_sha256=sha(R/'lean/Rc9_Top.lean'),delta=ledger['delta'])
dump('ARQ_VALIDATION.json',summary)
(E/'ARQ_attempts.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in receipts))
print(json.dumps(summary,indent=2))
