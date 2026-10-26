"""Offline audit of task sources, receipts and the unchanged atomic ledger."""
from pathlib import Path
from collections import Counter
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent; R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text())
standard={'propext','Classical.choice','Quot.sound'}
records=[];passed={}
for p in sorted(E.glob('SCG_[0-9][0-9][0-9]/receipt.json')):
 d=load(p);records.append(d)
 assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(d['swaps'])==0
 assert '-M7000' in d['command'] and '-j1' in d['command']
 for f,h in d['source_hashes'].items():assert sha(p.parent/'sources'/f)==h
 if d['exit_status']!=0:continue
 assert 'error:' not in (p.parent/'stdout.log').read_text()
 for line in d['print_axioms']:
  assert 'sorryAx' not in line
  m=re.search(r'depends on axioms: \[([^\]]*)\]',line)
  if m:assert set(map(str.strip,m[1].split(',')))<=standard
 for f,h in d['source_hashes'].items():
  if (R/'lean'/f).exists() and sha(R/'lean'/f)==h:passed[f]=d['attempt']
modules=sorted((R/'lean').glob('SCG_*.lean'))
for p in modules:
 assert p.name in passed,('unchecked current source',p.name)
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M),p
assert len(records)<=100
root=R/'lean/Rc7_Top.lean'
assert root.read_bytes()==(E/'SCG_BEFORE.lean.txt').read_bytes()==(E/'SCG_AFTER.lean.txt').read_bytes()
# Expand all inherited structure families freshly, preserving quantified guards.
catalog={};audits=[]
for item in load(E/'SCG_audit_plan.json'):
 p=E/item['attempt'];d=load(p/'receipt.json');assert d['exit_status']==0
 audits.append(dict(**item,stdout_sha256=sha(p/'stdout.log')))
 s=(p/'stdout.log').read_text()
 for b in re.split(r'(?=^structure )',s,flags=re.M):
  if not b.startswith('structure ') or 'fields:\n' not in b:continue
  k=re.match(r'structure (\S+)',b)[1]
  fields=b.split('fields:\n',1)[1].split('constructor:',1)[0]
  catalog[k]=dict(fields=fields,field_names=re.findall(r'^  ([\w.α-ωΑ-Ω]+) :',fields,re.M))
oldcatalog=load(R/'evidence/rejected-prefix-20261026/RPx_field_catalog.json')
compared=[]
for k in catalog.keys() & oldcatalog.keys():
 assert catalog[k]['fields']==oldcatalog[k]['fields'],('changed structure',k)
 compared.append(k)
assert len(compared)>=30,len(compared)
(E/'SCG_field_catalog.json').write_text(json.dumps(catalog,indent=2)+'\n')
old=load(R/'evidence/rejected-prefix-20261026/RPx_premises.json');rows=old['rows'];counts={}
for scope in ['actual antecedent','deployment only','deployment alias']:
 c=Counter(r['classification'] for r in rows if r['scope']==scope)
 counts[scope]={k:c[k] for k in 'TPGC'};assert counts[scope]==old['counts'][scope]
for name,selected in [('deduplicated actual plus non-alias deployment',[r for r in rows if r['scope']!='deployment alias']),('all audit rows',rows)]:
 c=Counter(r['classification'] for r in selected);counts[name]={k:c[k] for k in 'TPGC'}
ledger=dict(actual_theorem='AspisR1.Rc7_Top.deployed',new_deployed_endpoint=None,
 method=old['method'],classification_citation=old['classification_citation'],rows=rows,
 counts=counts,removed_rows=[],added_rows=[],reclassified_rows=[],
 delta={scope:{k:0 for k in 'TPGC'} for scope in counts},
 fresh_field_comparisons=sorted(compared),fresh_audits=audits,
 caveat='No SCG_Top.deployed; native/code/cut intermediate lemmas are not actual-top premise removals.')
(E/'SCG_LEDGER_DELTA.json').write_text(json.dumps(ledger,indent=2)+'\n')
summary=dict(compiler_invocations=len(records),passes=sum(d['exit_status']==0 for d in records),
 failures=sum(d['exit_status']!=0 for d in records),budget_max=100,budget_exhausted=len(records)==100,
 Kani=0,dependency_builds=0,package_replays=0,
 wall_seconds=sum(d['wall_seconds'] for d in records),peak_rss_kib=max(int(d['peak_rss_kib']) for d in records),swaps=0,
 current_modules={p.name:dict(sha256=sha(p),passing_attempt=passed[p.name]) for p in modules},
 current_deployed_root_sha256=sha(root),actual_premises_removed=0,
 field_comparisons=len(compared),remaining='SCG_COMPOSITION_MISMATCH.md; target not yet established')
(E/'SCG_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='current_modules'},indent=2))
