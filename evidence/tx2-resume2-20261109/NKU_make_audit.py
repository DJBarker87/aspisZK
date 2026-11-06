from pathlib import Path
import json,re,hashlib,difflib,shutil
E=Path(__file__).resolve().parent;P=E.parent/'tx2-resume-20261108'
excluded={'NKU_EndProbe','NKU_ProofDriver','NKU_Driver','NKU_COMBINED_IMPORT'}
receipts={}
for p in E.glob('NKU_L*/receipt.json'):
 x=json.loads(p.read_text())
 if x['kind']=='lean' and x['exit_status']==0:
  for n,h in x['source_hashes'].items():
   if n.endswith('.lean'):receipts[(Path(n).stem,h)]=str(p.relative_to(E))
modules=[];roots=[];selected={}
for p in sorted(E.glob('NKU_*.lean')):
 if p.stem in excluded:continue
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 if (p.stem,sha) not in receipts:continue
 modules.append(p.stem);selected[p.stem]=dict(sha256=sha,receipt=receipts[(p.stem,sha)])
 s=p.read_text();m=re.search(r'^namespace (\S+)',s,re.M)
 if m:roots.extend(m[1]+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M))
roots+=['AspisR1.RPx_Deployed.deployed']
assert len(roots)==len(set(roots))
groups=[roots[i:i+8] for i in range(0,len(roots),8)]
for name,obj in [('NKU_MODULES.json',modules),('NKU_SELECTED_SOURCES.json',selected),('NKU_AUDIT_ROOTS.json',dict(roots=roots,groups=groups))]:(E/name).write_text(json.dumps(obj,indent=2)+'\n')
(E/'NKU_COMBINED_IMPORT.lean').write_text('import NKN_COMBINED_IMPORT\nimport NKK_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in modules)+''.join('#print axioms '+r+'\n' for r in roots))
s=(P/'NKK_ProofDriver.lean').read_text();a=s.index('    else if mode == "proof0"');b=s.index('    else (#[], #[])',a)
s=s[:a]+''.join('    else if mode == "proof'+str(i)+'" then\n      (#[`NKU_COMBINED_IMPORT], #['+', '.join('`'+r for r in g)+'])\n' for i,g in enumerate(groups))+s[b:]
(E/'NKU_ProofDriver.lean').write_text(s)
(E/'NKU_PROOF_DRIVER.diff').write_text(''.join(difflib.unified_diff((P/'NKK_ProofDriver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NKK_ProofDriver.lean',tofile='NKU_ProofDriver.lean')))
s=(P/'NKK_Driver.lean').read_text().replace('NKK','NKU');(E/'NKU_Driver.lean').write_text(s)
(E/'NKU_SCAN_DRIVER.diff').write_text(''.join(difflib.unified_diff((P/'NKK_Driver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NKK_Driver.lean',tofile='NKU_Driver.lean')))
(E/'NKU_batch.py').write_text((P/'NKK_batch.py').read_text().replace('NKK','NKU'))
expected={}
for p in [P/'NKK_EXPECTED_IMPORTS.jsonl',E.parent/'ledger19-20261108/NKN_EXPECTED_IMPORTS.jsonl']:
 for line in p.read_text().splitlines():
  x=json.loads(line)
  if x['module'] in expected:assert expected[x['module']]==x,(x,expected[x['module']])
  else:expected[x['module']]=x
for m in modules+['NKU_COMBINED_IMPORT']:
 s=(E/(m+'.lean')).read_text();expected[m]=dict(module=m,imports=['Init']+re.findall(r'^import (\S+)',s,re.M))
(E/'NKU_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(expected[m])+'\n' for m in sorted(expected)))
(E/'NKU_native').mkdir(exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:shutil.copy2(P/'NKK_native'/n,E/'NKU_native'/n)
(E/'NKU_WALKER_PIN.json').write_text(json.dumps(dict(predecessor='evidence/tx2-resume-20261108/NKK_WALKER_PIN.json',predecessor_sha256=hashlib.sha256((P/'NKK_WALKER_PIN.json').read_bytes()).hexdigest(),walker_unchanged=True,selector_changes_only=True,full_combined_audit_limit=2),indent=2)+'\n')
print(json.dumps(dict(modules=len(modules),roots=len(roots),groups=len(groups))))
