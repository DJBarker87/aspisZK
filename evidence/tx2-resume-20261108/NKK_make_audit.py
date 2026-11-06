from pathlib import Path
import json,re,hashlib,difflib
E=Path(__file__).resolve().parent;P=E.parent/'tx2-native8-20261108'
excluded={'NKK_Inventory','NKK_PrintOps','NKK_ProofDriver','NKK_Driver','NKK_COMBINED_IMPORT'}
receipts={}
for p in E.glob('NKK_L*/receipt.json'):
 x=json.loads(p.read_text())
 if x['kind']=='lean' and x['exit_status']==0:
  for n,h in x['source_hashes'].items():
   if n.endswith('.lean'):receipts[(Path(n).stem,h)]=str(p.relative_to(E))
modules=[];roots=[];selected={}
for p in sorted(E.glob('NKK_*.lean')):
 if p.stem in excluded:continue
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 if (p.stem,sha) not in receipts:continue
 modules.append(p.stem);selected[p.stem]=dict(sha256=sha,receipt=receipts[(p.stem,sha)])
 s=p.read_text();m=re.search(r'^namespace (\S+)',s,re.M)
 if m:roots.extend(m[1]+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M))
roots+=['NJU_ResumeRoot.source','NJU_ResumeRoot.cohort','AspisR1.RPx_Deployed.deployed']
assert len(roots)==len(set(roots)), 'duplicate roots'
groups=[roots[i:i+10] for i in range(0,len(roots),10)]
for name,obj in [('NKK_MODULES.json',modules),('NKK_SELECTED_SOURCES.json',selected),('NKK_AUDIT_ROOTS.json',dict(roots=roots,groups=groups))]: (E/name).write_text(json.dumps(obj,indent=2)+'\n')
(E/'NKK_COMBINED_IMPORT.lean').write_text('import NKH_COMBINED_IMPORT\nimport NJU_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in modules)+''.join('#print axioms '+r+'\n' for r in roots))
s=(P/'NJU_ProofDriver.lean').read_text();a=s.index('    else if mode == "proof0"');b=s.index('    else (#[], #[])',a)
s=s[:a]+''.join('    else if mode == "proof'+str(i)+'" then\n      (#[`NKK_COMBINED_IMPORT], #['+', '.join('`'+r for r in g)+'])\n' for i,g in enumerate(groups))+s[b:]
(E/'NKK_ProofDriver.lean').write_text(s)
(E/'NKK_PROOF_DRIVER.diff').write_text(''.join(difflib.unified_diff((P/'NJU_ProofDriver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NJU_ProofDriver.lean',tofile='NKK_ProofDriver.lean')))
s=(P/'NJU_Driver.lean').read_text().replace('NJU','NKK');(E/'NKK_Driver.lean').write_text(s)
(E/'NKK_SCAN_DRIVER.diff').write_text(''.join(difflib.unified_diff((P/'NJU_Driver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NJU_Driver.lean',tofile='NKK_Driver.lean')))
(E/'NKK_batch.py').write_text((P/'NJU_batch.py').read_text().replace('NJU','NKK'))
expected={json.loads(s)['module']:json.loads(s) for s in (E.parent/'ledger18-20261108/NKH_EXPECTED_IMPORTS.jsonl').read_text().splitlines()}
for p in [P/'NJU_EXPECTED_IMPORTS.jsonl']:
 for line in p.read_text().splitlines():
  x=json.loads(line)
  if x['module'] in expected:assert expected[x['module']]==x,(x,expected[x['module']])
  else:expected[x['module']]=x
for m in modules+['NKK_COMBINED_IMPORT']:
 s=(E/(m+'.lean')).read_text();expected[m]=dict(module=m,imports=['Init']+re.findall(r'^import (\S+)',s,re.M))
(E/'NKK_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(expected[m])+'\n' for m in sorted(expected)))
(E/'NKK_native').mkdir(exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:(E/'NKK_native'/n).write_bytes((P/'NJU_native'/n).read_bytes())
(E/'NKK_WALKER_PIN.json').write_text(json.dumps(dict(predecessor='evidence/tx2-native8-20261108/NJU_WALKER_PIN.json',predecessor_sha256=hashlib.sha256((P/'NJU_WALKER_PIN.json').read_bytes()).hexdigest(),walker_unchanged=True,selector_changes_only=True,full_combined_audit_limit=2),indent=2)+'\n')
print(json.dumps(dict(modules=len(modules),roots=len(roots),groups=len(groups))))
