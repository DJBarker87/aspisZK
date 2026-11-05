"""Generate root/module lists only; retain the admitted walker/audit suffix."""
from pathlib import Path
import json,re,difflib
E=Path(__file__).resolve().parent
mods=[x['module'] for x in json.loads((E/'NIL_MODULES.json').read_text())['selected']]
roots=[]
for m in mods:
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 roots += [ns+'.'+name for name in re.findall(r'^theorem (\w+)',s,re.M)]
roots+=['AspisR1.RPx_Deployed.deployed']
combined='import NGK_COMBINED_IMPORT\nimport NID_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in mods)+'\n'+''.join('#check '+n+'\n#print axioms '+n+'\n' for n in roots)
(E/'NIL_COMBINED_IMPORT.lean').write_text(combined)
groups=[roots[i:i+20] for i in range(0,len(roots),20)]
(E/'NIL_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=groups),indent=2)+'\n')
s=(E/'NIL_ProofDriver.template.txt').read_text();branches=''
for i,g in enumerate(groups):branches+='    else if mode == "proof'+str(i)+'" then\n      (#[`NIL_COMBINED_IMPORT], #['+', '.join('`'+n for n in g)+'])\n'
s=s.replace('__NIL_ROOT_BRANCHES__\n',branches);(E/'NIL_ProofDriver.lean').write_text(s)
old=Path('evidence/tx2-native-20261106/NHV_ProofDriver.lean').read_text();(E/'NIL_PROOF_DRIVER.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='NHV_ProofDriver.lean',tofile='NIL_ProofDriver.lean')))
rows=[json.loads(l) for l in Path('evidence/tx2-native2-20261107/NID_LOADED_scan.jsonl').read_text().splitlines()]
expect={r['module']:r['imports'] for r in rows}
for m in mods+['NIL_COMBINED_IMPORT']:
 imports=['Init']
 for n in re.findall(r'^import (.+)$',(E/(m+'.lean')).read_text(),re.M):
  for part in n.split():
   if part not in imports:imports.append(part)
 expect[m]=imports
(E/'NIL_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=im))+'\n' for n,im in sorted(expect.items())))
(E/'NIL_Statements.lean').write_text('import NIL_COMBINED_IMPORT\nset_option pp.universes true\n'+''.join('#check @'+r+'\n' for r in roots))
print(json.dumps(dict(modules=len(mods),roots=len(roots),groups=len(groups))))
