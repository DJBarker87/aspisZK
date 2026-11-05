"""Generate root/module lists only; retain the admitted walker/audit suffix."""
from pathlib import Path
import json,re,difflib
E=Path(__file__).resolve().parent
mods=['NID_ResumeCanonical','NID_ResumeFields','NID_ResumeCallerDomain','NID_ResumeQuery','NID_MerkleLeafPacket','NID_BoundedReaders','NID_ReadListTransport','NID_WeightReadsTransport','NID_ReadStepFrame','NID_WithKTransport','NID_SemanticTransport','NID_RawOffsetCover','NID_TailView','NID_FinishAlpha','NID_RawWindowFrame','NID_NCI_QueryInvariant','NID_ResumeQueries','NID_KOffsetCover','NID_KmxComposition']
(E/'NID_MODULES.json').write_text(json.dumps(mods,indent=2)+'\n');roots=[]
for m in mods:
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 roots += [ns+'.'+name for name in re.findall(r'^theorem (\w+)',s,re.M)]
roots+=['AspisR1.RPx_Deployed.deployed']
combined='import NGK_COMBINED_IMPORT\nimport NHV_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in mods)+'\n'+''.join('#check '+n+'\n#print axioms '+n+'\n' for n in roots)
(E/'NID_COMBINED_IMPORT.lean').write_text(combined)
groups=[roots[i:i+20] for i in range(0,len(roots),20)]
(E/'NID_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=groups),indent=2)+'\n')
s=(E/'NID_ProofDriver.template.txt').read_text();branches=''
for i,g in enumerate(groups):branches+='    else if mode == "proof'+str(i)+'" then\n      (#[`NID_COMBINED_IMPORT], #['+', '.join('`'+n for n in g)+'])\n'
s=s.replace('__NID_ROOT_BRANCHES__\n',branches);(E/'NID_ProofDriver.lean').write_text(s)
old=Path('evidence/tx2-native-20261106/NHV_ProofDriver.lean').read_text();(E/'NID_PROOF_DRIVER.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='NHV_ProofDriver.lean',tofile='NID_ProofDriver.lean')))
rows=[json.loads(l) for l in Path('evidence/tx2-native-20261106/NHV_LOADED_scan.jsonl').read_text().splitlines()]
expect={r['module']:r['imports'] for r in rows}
for m in mods+['NID_COMBINED_IMPORT']:
 imports=['Init']
 for n in re.findall(r'^import (.+)$',(E/(m+'.lean')).read_text(),re.M):
  for part in n.split():
   if part not in imports:imports.append(part)
 expect[m]=imports
(E/'NID_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=im))+'\n' for n,im in sorted(expect.items())))
(E/'NID_Statements.lean').write_text('import NID_COMBINED_IMPORT\nset_option pp.universes true\n#print NID_ResumeFields.Domain\n'+''.join('#check @'+r+'\n' for r in roots))
print(json.dumps(dict(modules=len(mods),roots=len(roots),groups=len(groups))))
