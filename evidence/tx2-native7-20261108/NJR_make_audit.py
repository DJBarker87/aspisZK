from pathlib import Path
import json,re,difflib,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'tx2-native6-20261108'
modules=['NJR_FinishWindows','NJR_Cuts','NJR_FinishPrepared','NJR_ReservationSites','NJR_ReaderCut','NJR_FlushComposition','NJR_FinishDomain','NJR_RootAudit']
roots=[]
for m in modules:
 s=(E/(m+'.lean')).read_text();match=re.search(r'^namespace (\S+)',s,re.M)
 if match: roots += [match[1]+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M)]
roots+=['AspisR1.NJF_Root.finish','AspisR1.RPx_Deployed.deployed'];groups=[roots[i:i+10] for i in range(0,len(roots),10)]
(E/'NJR_MODULES.json').write_text(json.dumps(modules,indent=2)+'\n');(E/'NJR_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=groups),indent=2)+'\n')
(E/'NJR_COMBINED_IMPORT.lean').write_text('\n'.join('import '+m for m in ['NJO_COMBINED_IMPORT','NJJ_COMBINED_IMPORT']+modules)+'\n'+'\n'.join('#print axioms '+r for r in roots)+'\n')
s=(P/'NJJ_ProofDriver.lean').read_text();a=s.index('    else if mode == "proof0"');b=s.index('    else (#[], #[])',a)
s=s[:a]+''.join('    else if mode == "proof'+str(i)+'" then\n      (#[`NJR_COMBINED_IMPORT], #['+', '.join('`'+r for r in g)+'])\n' for i,g in enumerate(groups))+s[b:]
(E/'NJR_ProofDriver.lean').write_text(s)
(E/'NJR_PROOF_DRIVER.diff').write_text(''.join(difflib.unified_diff((P/'NJJ_ProofDriver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NJJ_ProofDriver.lean',tofile='NJR_ProofDriver.lean')))
s=(P/'NJJ_Driver.lean').read_text().replace('NJJ','NJR');(E/'NJR_Driver.lean').write_text(s)
(E/'NJR_SCAN_DRIVER.diff').write_text(''.join(difflib.unified_diff((P/'NJJ_Driver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NJJ_Driver.lean',tofile='NJR_Driver.lean')))
(E/'NJR_batch.py').write_text((P/'NJJ_batch.py').read_text().replace('NJJ','NJR'))
expected={}
for source in [E.parent/'ledger15-20261108/NJO_EXPECTED_IMPORTS.jsonl',P/'NJJ_EXPECTED_IMPORTS.jsonl']:
 for line in source.read_text().splitlines():
  row=json.loads(line);m=row['module']
  if m in expected:assert expected[m]==row,('coherent imports mismatch',m)
  expected[m]=row
for m in modules+['NJR_COMBINED_IMPORT']:
 s=(E/(m+'.lean')).read_text();expected[m]=dict(module=m,imports=['Init']+re.findall(r'^import (\S+)',s,re.M))
(E/'NJR_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(expected[m])+'\n' for m in sorted(expected)))
(E/'NJR_native').mkdir(exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:(E/'NJR_native'/n).write_bytes((P/'NJJ_native'/n).read_bytes())
(E/'NJR_WALKER_PIN.json').write_text(json.dumps(dict(predecessor=str(P/'NJJ_WALKER_PIN.json'),predecessor_sha256=hashlib.sha256((P/'NJJ_WALKER_PIN.json').read_bytes()).hexdigest(),walker_unchanged=True,driver_changes='module/root selector and receipt paths only, per ax2'),indent=2)+'\n')
for n in ['final_checks','cleanup']:(E/f'NJR_{n}.py').write_text((P/f'NJJ_{n}.py').read_text().replace('NJJ','NJR'))
print(json.dumps(dict(modules=len(modules),roots=len(roots),groups=len(groups))))
