from pathlib import Path
import json,re,hashlib,difflib
E=Path(__file__).resolve().parent;P=E.parent/'tx2-native4-20261107'
selected={}
for p in sorted(E.glob('NJC_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());m=r['module'];src=E/(m+'.lean')
 if r['kind']!='lean' or r['exit_status']!=0 or not src.exists() or m in ['NJC_Inspect','NJC_Driver','NJC_ProofDriver','NJC_COMBINED_IMPORT']:continue
 if r['source_hashes'].get('NJC_generated/'+m+'.lean')!=hashlib.sha256(src.read_bytes()).hexdigest():continue
 selected[m]=dict(module=m,receipt=str(p.relative_to(E)),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest())
mods=list(selected);roots=[]
for m in mods:
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 roots += [ns+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M)]
 if m=='NJC_CutTypes':roots += [ns+'.'+n for n in ['readerK','powers','weightStep']]
roots+=['AspisR1.RPx_Deployed.deployed'];groups=[roots[i:i+15] for i in range(0,len(roots),15)]
(E/'NJC_MODULES.json').write_text(json.dumps(dict(selected=list(selected.values())),indent=1)+'\n')
(E/'NJC_COMBINED_IMPORT.lean').write_text('import NGK_COMBINED_IMPORT\nimport NIU_COMBINED_IMPORT\nimport NIY_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in mods)+'\n'+''.join('#check '+n+'\n#print axioms '+n+'\n' for n in roots))
(E/'NJC_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=groups),indent=1)+'\n')
s=(P/'NIY_ProofDriver.lean').read_text();a=s.index('    else if mode == "proof0"');b=s.index('    else (#[], #[])',a)
branches=''
for i,g in enumerate(groups):branches+='    else if mode == "proof'+str(i)+'" then\n      (#[`NJC_COMBINED_IMPORT], #['+', '.join('`'+n for n in g)+'])\n'
s=s[:a]+branches+s[b:];(E/'NJC_ProofDriver.lean').write_text(s)
(E/'NJC_PROOF_DRIVER.diff').write_text(''.join(difflib.unified_diff((P/'NIY_ProofDriver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NIY_ProofDriver.lean',tofile='NJC_ProofDriver.lean')))
s=(P/'NIY_Driver.lean').read_text().replace('NIY_','NJC_');(E/'NJC_Driver.lean').write_text(s)
(E/'NJC_SCAN_DRIVER.diff').write_text(''.join(difflib.unified_diff((P/'NIY_Driver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NIY_Driver.lean',tofile='NJC_Driver.lean')))
(E/'NJC_batch.py').write_text((P/'NIY_batch.py').read_text().replace('NIY_','NJC_'))
expect={};conflicts=[]
for p in [E.parent/'ledger13-20261107/NIU_EXPECTED_IMPORTS.jsonl',P/'NIY_EXPECTED_IMPORTS.jsonl']:
 for line in p.read_text().splitlines():
  r=json.loads(line)
  if r['module'] in expect and expect[r['module']]!=r['imports']:conflicts.append(dict(module=r['module'],first=expect[r['module']],second=r['imports']))
  else:expect[r['module']]=r['imports']
for m in mods+['NJC_COMBINED_IMPORT']:
 expect[m]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',(E/(m+'.lean')).read_text(),re.M)))
(E/'NJC_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=v))+'\n' for n,v in sorted(expect.items())))
(E/'NJC_EXPECTED_CONFLICTS.json').write_text(json.dumps(conflicts,indent=1)+'\n')
(E/'NJC_native').mkdir(exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:(E/'NJC_native'/n).write_bytes((P/'NIY_native'/n).read_bytes())
walker=E.parent/'axaudit2-20261102/NEP_WALKER.lean';(E/'NJC_WALKER_SOURCE.lean.txt').write_bytes(walker.read_bytes())
(E/'NJC_WALKER_PIN.json').write_text(json.dumps(dict(path=str(walker),sha256=hashlib.sha256(walker.read_bytes()).hexdigest(),algorithm='unchanged NEP walker and unchanged retained C; driver lists/runtime only'),indent=1)+'\n')
print(json.dumps(dict(modules=len(mods),roots=len(roots),expected_conflicts=len(conflicts))))
