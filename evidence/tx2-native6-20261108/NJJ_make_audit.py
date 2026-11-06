from pathlib import Path
import json,re,difflib,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'tx2-native5-20261107'
modules=['NJJ_Any','NJJ_AnyExit','NJJ_Chunks','NJJ_ChunksRemainder','NJJ_Cuts','NJJ_RowWindow','NJJ_QueryOps','NJJ_Value','NJJ_Projection','NJJ_Common','NJJ_DomainAudit','NJJ_ResumeDomains','NJJ_Constructors','NJJ_Pending','NJJ_PendingStep','NJJ_Flush']
roots=[]
for m in modules:
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 roots.extend(ns+'.'+name for name in re.findall(r'^theorem (\w+)',s,re.M))
roots.append('AspisR1.RPx_Deployed.deployed');groups=[roots[i:i+10] for i in range(0,len(roots),10)]
(E/'NJJ_MODULES.json').write_text(json.dumps(modules,indent=2)+'\n');(E/'NJJ_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=groups,roots=roots),indent=2)+'\n')
(E/'NJJ_COMBINED_IMPORT.lean').write_text('\n'.join('import '+m for m in ['NGK_COMBINED_IMPORT','NIU_COMBINED_IMPORT','NJC_COMBINED_IMPORT']+modules)+'\n'+ '\n'.join('#print axioms '+r for r in roots)+'\n')
s=(P/'NJC_ProofDriver.lean').read_text();a=s.index('    else if mode == "proof0"');b=s.index('    else (#[], #[])',a)
s=s[:a]+''.join('    else if mode == "proof'+str(i)+'" then\n      (#[`NJJ_COMBINED_IMPORT], #['+', '.join('`'+r for r in g)+'])\n' for i,g in enumerate(groups))+s[b:]
(E/'NJJ_ProofDriver.lean').write_text(s)
(E/'NJJ_PROOF_DRIVER.diff').write_text(''.join(difflib.unified_diff((P/'NJC_ProofDriver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NJC_ProofDriver.lean',tofile='NJJ_ProofDriver.lean')))
s=(P/'NJC_Driver.lean').read_text().replace('NJC','NJJ');(E/'NJJ_Driver.lean').write_text(s)
(E/'NJJ_SCAN_DRIVER.diff').write_text(''.join(difflib.unified_diff((P/'NJC_Driver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NJC_Driver.lean',tofile='NJJ_Driver.lean')))
(E/'NJJ_batch.py').write_text((P/'NJC_batch.py').read_text().replace('NJC','NJJ'))
expected={r['module']:r for r in map(json.loads,(P/'NJC_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for m in modules+['NJJ_COMBINED_IMPORT']:
 s=(E/(m+'.lean')).read_text();expected[m]=dict(module=m,imports=['Init']+re.findall(r'^import (\S+)',s,re.M))
(E/'NJJ_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(expected[m])+'\n' for m in sorted(expected)))
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 (E/'NJJ_native').mkdir(exist_ok=True);(E/'NJJ_native'/n).write_bytes((P/'NJC_native'/n).read_bytes())
(E/'NJJ_WALKER_SOURCE.lean.txt').write_bytes((P/'NJC_WALKER_SOURCE.lean.txt').read_bytes())
(E/'NJJ_WALKER_PIN.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256((E/'NJJ_WALKER_SOURCE.lean.txt').read_bytes()).hexdigest(),predecessor_pin=json.loads((P/'NJC_WALKER_PIN.json').read_text()),walker_unchanged=True,driver_changes='module/root lists and receipt paths only; runtime setup unchanged'),indent=2)+'\n')
print(json.dumps(dict(modules=len(modules),roots=len(roots),groups=len(groups))))
