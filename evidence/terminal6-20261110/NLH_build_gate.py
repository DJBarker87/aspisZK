from pathlib import Path
import json,re,hashlib,subprocess,difflib
p=Path(__file__).resolve().parent;sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
rows=[json.loads(l)for l in(p/'NLH_ATTEMPTS.jsonl').read_text().splitlines()];passed={}
excluded={'NLH_Driver','NLH_ProofDriver','NLH_COMBINED_IMPORT'}
for r in rows:
 m=r.get('module','');q=p/(m+'.lean')
 if r.get('kind')=='lean'and r['exit_status']==0 and q.exists()and m not in excluded and r['source_hashes'].get(q.name)==sha(q):passed[m]=r
roots=[];pins=[]
for m,r in sorted(passed.items()):
 names=[re.match(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",s)[1]for s in r['print_axioms']if re.match(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",s)]
 assert not any('sorryAx'in s for s in r['print_axioms']),m
 count=len(re.findall(r'^(?:private\s+|protected\s+)?theorem\s+', (p/(m+'.lean')).read_text(),re.M));assert len(set(names))>=count,(m,count,len(names));roots+=names;pins.append(dict(module=m,source_sha256=sha(p/(m+'.lean')),attempt=r['attempt'],printed_roots=names))
expected={};allroots=[];baseline=[]
for directory,prefix in [('ledger20-20261109','NKW'),('terminal5-20261108','NKR'),('row-bridges-20261109','NKY')]:
 b=p.parent/directory
 for suffix in ['_AUDIT_ROOTS.json','_EXPECTED_IMPORTS.jsonl']:
  q=b/(prefix+suffix);baseline.append(dict(path=str(q),sha256=sha(q)))
  if suffix.endswith('ROOTS.json'):
   d=json.loads(q.read_text());allroots+=d['roots']if'roots'in d else sum(d['groups'],[])
  else:
   for v in map(json.loads,q.read_text().splitlines()):
    assert v['module']not in expected or expected[v['module']]==v['imports'],v['module']
    expected[v['module']]=v['imports']
nkr=json.loads((p.parent/'terminal5-20261108/NKR_GATE_SOURCES.json').read_text())['passed']
imports=['NKW_COMBINED_IMPORT','NKY_COMBINED_IMPORT']+sorted(nkr)+sorted(passed)
text=''.join('import '+m+'\n'for m in dict.fromkeys(imports))+'\n#print axioms AspisR1.RPx_Deployed.deployed\n'
# GATE REPAIR: private helpers are NEVER elaborated through source-level #check.
# Their complete raw names stay in the private-aware audit inventory below.
(p/'NLH_COMBINED_IMPORT.lean').write_text(text)
for m in passed|{'NLH_COMBINED_IMPORT':{}}:
 q=p/(m+'.lean');expected[m]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',q.read_text(),re.M)))
allroots=sorted(set(allroots+roots+['AspisR1.RPx_Deployed.deployed']));private='_private.NKR_SumCopyFull.0.AspisR1.NKR_SumCopyRoot.rows_ext';assert private in allroots
count=int(__import__('sys').argv[1])if len(__import__('sys').argv)>1 else 26
# Cost-balanced initial partition, using retained predecessor raw edge counts.
# This is a new audit partition, never a rerun of a timed-out shape.
cost={};cost_pins=[]
for q in sorted((p.parent/'terminal5-20261108/NKR_audit').glob('proof*/receipt.json')):
 d=json.loads(q.read_text());cost_pins.append(dict(path=str(q),sha256=sha(q)))
 for row in d.get('results',[]):cost[row['root']]=row['edges_scanned']
unknown=100000;groups=[[]for _ in range(count)];loads=[0]*count
for root in sorted(allroots,key=lambda r:(-cost.get(r,unknown),r)):
 i=min(range(count),key=lambda j:(loads[j],j));groups[i].append(root);loads[i]+=cost.get(root,unknown)
for g in groups:g.sort()
(p/'NLH_AUDIT_PARTITION.json').write_text(json.dumps(dict(method='largest-first edge-count balancing from predecessor raw receipts',predecessor_receipts=cost_pins,groups=count,estimated_edges=loads,unknown_root_edges=unknown,known_costs=len(cost)),indent=1)+'\n')
assert len(set(sum(groups,[])))==sum(map(len,groups))==len(allroots)
(p/'NLH_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=allroots,groups=groups,new_roots=sorted(set(roots)),baseline_pins=baseline,private_inventory_retained=True),indent=1)+'\n');(p/'NLH_AUDIT_MODULES.json').write_text(json.dumps([['NLH_COMBINED_IMPORT']]*count)+'\n');(p/'NLH_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=im))+'\n'for m,im in sorted(expected.items())))
(p/'NLH_GATE_SOURCES.json').write_text(json.dumps(dict(passed={m:r['attempt']for m,r in passed.items()},sources=pins,baselines=baseline,nkr_modules=list(nkr),combined_sha256=sha(p/'NLH_COMBINED_IMPORT.lean'),gate_generator_private_source_checks=False,raw_private_inventory_complete=True),indent=1)+'\n')
print(json.dumps(dict(own_modules=len(passed),new_roots=len(set(roots)),total_roots=len(allroots),groups=count,combined_attempts_max=2)))
