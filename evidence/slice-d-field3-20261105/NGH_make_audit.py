from pathlib import Path
import json,re,hashlib,difflib
E=Path(__file__).resolve().parent;A=E.parent/'slice-d-field2-20261104'
mods=['NGH_AccumulateRef','NGH_SmallRef','NGH_SmallValue','NGH_QSquareRef','NGH_QSquareOps','NGH_CMWords','NGH_WideBridge','NGH_CellComposition','NGH_OuterRef']
roots=[]
for m in mods:
 roots += re.findall(r'^#print axioms (\w+)',(E/(m+'.lean')).read_text(),re.M)
# Rebuild names with namespace per source, no guessing declaration ownership.
roots=[m+'.'+t for m in mods for t in re.findall(r'^#print axioms (\w+)',(E/(m+'.lean')).read_text(),re.M)]+['AspisR1.RPx_Deployed.deployed']
(E/'NGH_AUDIT_ROOTS.json').write_text(json.dumps(dict(modules=mods,roots=roots),indent=1)+'\n')
combined='import NGA_COMBINED_IMPORT\n'+''.join('import '+m+'\n'for m in mods)+''.join('#print axioms '+r+'\n'for r in roots)
(E/'NGH_COMBINED_IMPORT.lean').write_text(combined)
s=(A/'NGA_Driver.lean').read_text();start=s.index('    else if mode == "proof0"');end=s.index('    else (#[], #[])',start)
s=s[:start]+''.join('    else if mode == "proof'+str(i//5)+'" then\n      (#[`NGH_COMBINED_IMPORT], #['+', '.join('`'+r for r in roots[i:i+5])+'])\n'for i in range(0,len(roots),5))+s[end:]
s=s.replace('NGA_COMBINED_IMPORT','NGH_COMBINED_IMPORT').replace('NGA_EXPECTED_IMPORTS','NGH_EXPECTED_IMPORTS').replace('NGA_LOADED','NGH_LOADED')
(E/'NGH_Driver.lean').write_text(s)
(E/'NGH_DRIVER.diff').write_text(''.join(difflib.unified_diff((A/'NGA_Driver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NGA_Driver.lean',tofile='NGH_Driver.lean')))
walker=A/'NGA_WALKER_SOURCE.lean.txt';(E/'NGH_WALKER_SOURCE.lean.txt').write_bytes(walker.read_bytes());pin=json.loads((A/'NGA_WALKER_PIN.json').read_text());assert hashlib.sha256(walker.read_bytes()).hexdigest()==pin['sha256'];(E/'NGH_WALKER_PIN.json').write_text(json.dumps(pin,indent=1)+'\n')
script=(A/'NGA_review_batch.py').read_text().replace('NGA','NGH');(E/'NGH_review_batch.py').write_text(script)
expected=[json.loads(l)for l in (A/'NGA_EXPECTED_IMPORTS.jsonl').read_text().splitlines()]
for m in mods+['NGH_COMBINED_IMPORT']:
 imports=['Init']+[n for l in (E/(m+'.lean')).read_text().splitlines() if l.startswith('import ') for n in l[7:].split()]
 expected.append(dict(module=m,imports=imports))
(E/'NGH_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(x)+'\n'for x in expected))
print(len(roots),'roots')
