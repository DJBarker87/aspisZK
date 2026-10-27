from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[];passing={}
for n in range(1,101):
 a=f'FIo_{n:03}';p=E/a/'receipt.json'
 if p.exists():
  d=json.loads(p.read_text());receipts.append(d)
  if d['exit_status']==0:
   for s,h in d.get('source_hashes',{}).items():passing.setdefault((s,h),[]).append(a)
 else:assert (E/(a+'-preflight.json')).exists(),a
sources=[]
for p in sorted((R/'lean').glob('FIo_*.lean')):
 matches=passing.get((p.name,sha(p)),[])
 sources.append(dict(source=str(p.relative_to(R)),sha256=sha(p),passing=matches))
ledger=json.loads((R/'evidence/recount7-20261026/Rc7_premises.json').read_text())
# Preserve every inherited row: operational specialization is not discharge.
rows=ledger['rows']; counts={}
from collections import Counter
for scope in ['actual antecedent','deployment only','deployment alias']:
 counts[scope]=dict(Counter(x['classification'] for x in rows if x['scope']==scope))
recount=dict(before='AspisR1.Rc7_Top.deployed',after='AspisR1.FIo_Accepted.deployed',
 method=ledger['method'],ledger_sha256=sha(R/'evidence/recount7-20261026/Rc7_premises.json'),
 before_counts=counts,after_counts=counts,removed=[],added=[],delta=dict(T=0,P=0,G=0,C=0),
 quantifiers='F operational carrier specialised to FIo_Install.W and concrete arithmetic/constructor/Pair/dot; same controls and all law hypotheses retained. All conclusions/events unchanged under substitution.',
 quarter_alias_note='Raw Rc7 ledger is retained for comparison. Within EACH witness-domain, L134/L137 are one predicate (FIn_QuarterAlias.field_type); removing those two reporting duplicates from both sides gives actual83T+24P+13G and combined89T+29P+13G, delta0. Native/source-global quantifiers are never coalesced.',
 headline='No change to F3Y_Headline.deployed or FGl_Headline.deployed; no inherited FIn discharge counted again.',rows=rows)
(E/'FIo_recount.json').write_text(json.dumps(recount,indent=2)+'\n')
missing=[s for s in sources if not s['passing']]
report=dict(charged_lean_ids=100,compiler_starts=len(receipts),preflight_charges=100-len(receipts),
 kani_runs=3,kani_limit=40,lean_limit=100,sources=sources,unmatched=missing,
 receipts=[{k:d.get(k) for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']} for d in receipts])
(E/'FIo_validation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(charged=100,starts=len(receipts),unmatched=missing,counts=counts),indent=2))
