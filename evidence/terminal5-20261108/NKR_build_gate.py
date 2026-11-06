from pathlib import Path
import json,re,hashlib,difflib
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rs=[json.loads(l)for l in(E/'NKR_ATTEMPTS.jsonl').read_text().splitlines()]
merged={Path(x['source']).stem for x in json.loads((E/'NKR_SumCombine_PROVENANCE.json').read_text())['inputs']if x['merged']}
excluded=merged|{'NKR_Inventory','NKR_Driver','NKR_ProofDriver','NKR_COMBINED_IMPORT'}
passed={}
for r in rs:
 m=r.get('module','');p=E/(m+'.lean')
 if r.get('kind')=='lean'and r['exit_status']==0 and m not in excluded and p.exists()and r['source_hashes'].get(p.name)==sha(p):passed[m]=r
roots=[];pins=[]
for m,r in sorted(passed.items()):
 lines=r['print_axioms'];names=[re.match(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",l)[1]for l in lines if re.match(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",l)]
 assert not any('sorryAx'in l for l in lines),m
 count=len(re.findall(r'^(?:@\[[^\]]+\]\s*)?(?:private\s+|protected\s+)?theorem\s+', (E/(m+'.lean')).read_text(),re.M))
 assert len(set(names))>=count,(m,count,len(names))
 roots+=names;pins.append(dict(module=m,path=m+'.lean',sha256=sha(E/(m+'.lean')),attempt=r['attempt'],new_top_theorems=count,printed_axioms=names))
roots=sorted(set(roots));base_roots=[];expected={};baseline=[]
for directory,prefix in [('ledger19-20261108','NKN'),('terminal4-20261108','NKI')]:
 b=E.parent/directory
 for suffix in ['_AUDIT_ROOTS.json','_EXPECTED_IMPORTS.jsonl']:
  p=b/(prefix+suffix);baseline.append(dict(path=str(p),sha256=sha(p)))
  if suffix.endswith('ROOTS.json'):base_roots+=json.loads(p.read_text())['roots']
  else:
   for row in map(json.loads,p.read_text().splitlines()):
    assert row['module']not in expected or expected[row['module']]==row['imports'],row['module']
    expected[row['module']]=row['imports']
allroots=sorted(set(base_roots+roots+['AspisR1.RPx_Deployed.deployed']))
s='import NKN_COMBINED_IMPORT\nimport NKI_COMBINED_IMPORT\n'+''.join('import '+m+'\n'for m in sorted(passed))
s+='\n#print axioms AspisR1.RPx_Deployed.deployed\n'
for name in roots:s+='#check '+name+'\n#print axioms '+name+'\n'
# Full root statements already printed in focused receipts; this gate checks
# every new theorem with the actual canonical-owner combined environment.
(E/'NKR_COMBINED_IMPORT.lean').write_text(s)
for p in[E/(m+'.lean')for m in passed]+[E/'NKR_COMBINED_IMPORT.lean']:
 expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'NKR_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=imports))+'\n'for m,imports in sorted(expected.items())))
count=28;groups=[allroots[i*len(allroots)//count:(i+1)*len(allroots)//count]for i in range(count)]
assert len(set(sum(groups,[])))==sum(map(len,groups))==len(allroots)
(E/'NKR_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=allroots,groups=groups,new_roots=roots,baseline_pins=baseline,reason='One complete disjoint union NKN+NKI+NKR proof-body audit with unchanged hardened walker'),indent=1))
(E/'NKR_AUDIT_MODULES.json').write_text(json.dumps([['NKR_COMBINED_IMPORT']]*count))
(E/'NKR_GATE_SOURCES.json').write_text(json.dumps(dict(passed={m:r['attempt']for m,r in passed.items()},source_extensions=pins,baselines=baseline,excluded_diagnostic_or_merged_modules=sorted(excluded),combined_sha256=sha(E/'NKR_COMBINED_IMPORT.lean')),indent=1))
print(json.dumps(dict(selected_modules=len(passed),new_roots=len(roots),total_raw_roots=len(allroots),groups=count)))
