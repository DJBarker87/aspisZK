"""Offline ARP receipts, source identity, unchanged endpoint and atomic recount."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent; R=E.parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(name,x): (E/name).write_text(json.dumps(x,indent=2)+'\n')
def norm(s): return re.sub(r'\s+',' ',s).strip()
receipts=[]
for p in sorted(E.glob('ARP_[0-9][0-9][0-9]/receipt.json')):
 x=json.loads(p.read_text()); receipts.append(x)
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert len(x['sources'])==1 and '-M7000' in x['command']
 assert int(x['swaps'])==0
 assert x['source_revision'] and x['deps_fingerprint']['selected_objects']
 for s in x['sources']: assert sha(p.parent/'sources'/s)==x['source_hashes'][s]
 if x['exit_status']==0:
  assert x['print_axioms']
  for line in x['print_axioms']:
   if 'does not depend on any axioms' in line: continue
   names=set(re.search(r'\[(.*)\]',line).group(1).split(', '))
   assert names <= {'propext','Classical.choice','Quot.sound'},line
 else: assert x['attempt']=='ARP_001'
assert len(receipts)==6<=100
manifest=json.loads((E/'ARP_HOST_MANIFEST.json').read_text())
for x in receipts:
 for name,entry in x['deps_fingerprint']['selected_objects'].items():
  if name.startswith('ARP_'): assert entry['sha256']==manifest[name]['sha256']
for p in (R/'lean').glob('ARP_*.lean'):
 assert manifest[p.name]['sha256']==sha(p)
 assert any(x['exit_status']==0 and x['source_hashes'].get(p.name)==sha(p) for x in receipts)
 assert not re.search(r'\b(sorry|admit|native_decide|maxHeartbeats|maxRecDepth)\b|^\s*axiom\s',p.read_text(),re.M)
for n in ['Rc9_Top.lean','SCE_FixtureData.lean','F3S_Join.lean']:
 assert manifest[n]['sha256']==sha(R/'lean'/n)
for before,after in [('ARP_BEFORE_SOURCE.lean.txt','ARP_AFTER_SOURCE.lean.txt'),('ARP_BEFORE_KERNEL.lean.txt','ARP_AFTER_KERNEL.lean.txt')]:
 assert norm((E/before).read_text())==norm((E/after).read_text())
assert sha(E/'ARP_BEFORE_SOURCE.lean.txt')==sha(R/'lean/Rc9_Top.lean')
assert '⋯' not in (E/'ARP_AFTER_KERNEL.lean.txt').read_text()
basefile=R/'evidence/recount9-20261026/Rc9_premises.json'; base=json.loads(basefile.read_text())
def tally(rs):
 return dict(rows=len(rs),classes={c:sum(r['classification']==c for r in rs) for c in ['T','P','G','C']},by_owner={o:{c:sum(r['classification']==c and r['owner']==o for r in rs) for c in ['T','P','G','C']} for o in ['lead','session A','external']})
def scopes(rs):
 return {s:tally([r for r in rs if r['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']}|{'deduplicated actual plus non-alias deployment':tally([r for r in rs if r['scope']!='deployment alias'])}
raw=scopes(base['rows']); distinct=scopes([r for r in base['rows'] if r['id']!='L137'])
assert raw==base['raw_counts'] and distinct==base['counts']
ledger=dict(actual_theorem='AspisR1.Rc9_Top.deployed',method=base['method'],baseline=str(basefile.relative_to(R)),baseline_sha256=sha(basefile),aliases=base['aliases'],rows=base['rows'],before=dict(raw=raw,distinct=distinct),after=dict(raw=raw,distinct=distinct),removed=[],added=[],reclassified=[],delta=dict(T=0,P=0,G=0,C=0),source_before_sha256=sha(E/'ARP_BEFORE_SOURCE.lean.txt'),source_after_sha256=sha(E/'ARP_AFTER_SOURCE.lean.txt'),kernel_before_sha256=sha(E/'ARP_BEFORE_KERNEL.lean.txt'),kernel_after_sha256=sha(E/'ARP_AFTER_KERNEL.lean.txt'),scope='No endpoint change. Diagnostic BankSupported is not a new top premise. Shared guards/witnesses and native/global families retained; no structure-bundling discount.')
dump('ARP_LEDGER_DELTA.json',ledger)
summary=dict(lean_attempts=len(receipts),passes=sum(x['exit_status']==0 for x in receipts),excluded=['ARP_001: missing explicit import, repaired in 002'],kani_runs=0,dependency_builds=0,total_lean_wall_seconds=sum(x['wall_seconds'] for x in receipts),peak_rss_kib=max(int(x['peak_rss_kib']) for x in receipts),swaps=0,budget_exhausted=False,stop='Explicit phase-1 composition stop: SAME SCE constant natives cannot have AeneasExtraction for any dictionary. No ARP_Join built.',final_target=receipts[-1]['sources'][0],final_receipt={k:receipts[-1][k] for k in ['attempt','source_revision','exit_status','wall_seconds','peak_rss_kib','swaps']},source_root_sha256=sha(R/'lean/Rc9_Top.lean'),delta=ledger['delta'])
dump('ARP_VALIDATION.json',summary)
(E/'ARP_attempts.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in receipts))
print(json.dumps(summary,indent=2))
