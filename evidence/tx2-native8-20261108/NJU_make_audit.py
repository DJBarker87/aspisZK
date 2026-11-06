from pathlib import Path
import json,re,hashlib,difflib
E=Path(__file__).resolve().parent;P=E.parent/'tx2-native7-20261108'
# Only exact current sources with a successful focused receipt are admissible.
excluded={'NJU_Inspect','NJU_ScalarInspect','NJU_ProofDriver','NJU_Driver','NJU_COMBINED_IMPORT'}
receipts={}
for r in E.glob('NJU_L*/receipt.json'):
 x=json.loads(r.read_text())
 if x['kind']=='lean' and x['exit_status']==0:
  for n,h in x['source_hashes'].items():
   if n.endswith('.lean'):receipts[(Path(n).stem,h)]=str(r.relative_to(E))
modules=[];roots=[];selected={}
for p in sorted(E.glob('NJU_*.lean')):
 if p.stem in excluded:continue
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 if (p.stem,sha) not in receipts:continue
 modules.append(p.stem);selected[p.stem]=dict(sha256=sha,receipt=receipts[(p.stem,sha)])
 s=p.read_text();m=re.search(r'^namespace (\S+)',s,re.M)
 if m:roots.extend(m[1]+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M))
if 'NJU_ResumeObserved' in modules:roots+=['NJU_ResumeObserved.run','NJU_ResumeObserved.runRef']
roots+=['AspisR1.NJF_Root.finish','AspisR1.RPx_Deployed.deployed']
groups=[roots[i:i+10] for i in range(0,len(roots),10)]
(E/'NJU_MODULES.json').write_text(json.dumps(modules,indent=2)+'\n')
(E/'NJU_SELECTED_SOURCES.json').write_text(json.dumps(selected,indent=2)+'\n')
(E/'NJU_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=groups),indent=2)+'\n')
(E/'NJU_COMBINED_IMPORT.lean').write_text('import NJO_COMBINED_IMPORT\nimport NJR_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in modules)+''.join('#print axioms '+r+'\n' for r in roots))
s=(P/'NJR_ProofDriver.lean').read_text();a=s.index('    else if mode == "proof0"');b=s.index('    else (#[], #[])',a)
s=s[:a]+''.join('    else if mode == "proof'+str(i)+'" then\n      (#[`NJU_COMBINED_IMPORT], #['+', '.join('`'+r for r in g)+'])\n' for i,g in enumerate(groups))+s[b:]
(E/'NJU_ProofDriver.lean').write_text(s)
(E/'NJU_PROOF_DRIVER.diff').write_text(''.join(difflib.unified_diff((P/'NJR_ProofDriver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NJR_ProofDriver.lean',tofile='NJU_ProofDriver.lean')))
s=(P/'NJR_Driver.lean').read_text().replace('NJR','NJU');(E/'NJU_Driver.lean').write_text(s)
(E/'NJU_SCAN_DRIVER.diff').write_text(''.join(difflib.unified_diff((P/'NJR_Driver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NJR_Driver.lean',tofile='NJU_Driver.lean')))
(E/'NJU_batch.py').write_text((P/'NJR_batch.py').read_text().replace('NJR','NJU'))
expected={json.loads(s)['module']:json.loads(s) for s in (P/'NJR_EXPECTED_IMPORTS.jsonl').read_text().splitlines()}
for m in modules+['NJU_COMBINED_IMPORT']:
 s=(E/(m+'.lean')).read_text();expected[m]=dict(module=m,imports=['Init']+re.findall(r'^import (\S+)',s,re.M))
(E/'NJU_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(expected[m])+'\n' for m in sorted(expected)))
(E/'NJU_native').mkdir(exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:(E/'NJU_native'/n).write_bytes((P/'NJR_native'/n).read_bytes())
(E/'NJU_WALKER_PIN.json').write_text(json.dumps(dict(predecessor='evidence/tx2-native7-20261108/NJR_WALKER_PIN.json',predecessor_sha256=hashlib.sha256((P/'NJR_WALKER_PIN.json').read_bytes()).hexdigest(),walker_unchanged=True,selector_changes_only=True),indent=2)+'\n')
for n in ['final_checks','cleanup']:(E/f'NJU_{n}.py').write_text((P/f'NJR_{n}.py').read_text().replace('NJR','NJU'))
print(json.dumps(dict(modules=len(modules),roots=len(roots),groups=len(groups))))
