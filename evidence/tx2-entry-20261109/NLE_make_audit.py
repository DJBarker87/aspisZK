from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
files=['NLE_AuthState','NLE_AuthParse','NLE_AuthMark','NLE_AuthFold','NLE_Length','NLE_SnapshotClause','NLE_RangeClause','NLE_ParseInstall','NLE_AuthScope','NLE_AuthLiteral','NLE_OwnedState','NLE_OwnedFold','NLE_OwnedSource','NLE_OwnedValidate','NLE_OwnedProof','NLE_OwnedCheckpoint','NLE_OwnedEncode','NLE_OwnedEmit','NLE_OwnedTx2','NLE_OwnedFine','NLE_MapError','NLE_ErrorPrefix','NLE_WrapperState','NLE_WrapperFold','NLE_WrapperSource','NLE_WrapperSteps','NLE_DispatchState','NLE_DispatchFold','NLE_EntryFold','NLE_RouteFold','NLE_NativeTags','NLE_SafeCuts','NLE_CallerScope']
roots=[]
for module in files:
 source=(E/(module+'.lean')).read_text();namespace=re.search(r'^namespace (\w+)',source,re.M)[1]
 roots.extend(namespace+'.'+name for name in re.findall(r'^theorem (\w+)',source,re.M))
roots+=['AspisR1.RPx_Deployed.deployed','NKU_ParentFold.source','NKU_ParentFold.cohort','NKU_ParentFold.clauses']
groups=[roots[i:i+8] for i in range(0,len(roots),8)]
(E/'NLE_AUDIT_MODULES.json').write_text(json.dumps(files+['NLE_COMBINED_IMPORT'],indent=1))
(E/'NLE_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=groups),indent=1))
source=Path('evidence/tx2-resume2-20261109/NKU_ProofDriver.lean').read_text();start=source.index('    else if mode == "proof0"');end=source.index('    else (#[], #[])',start)
selected=''
for i,group in enumerate(groups):selected+='    else if mode == "proof'+str(i)+'" then\n      (#[`NLE_COMBINED_IMPORT], #['+', '.join('`'+r for r in group)+'])\n'
(E/'NLE_ProofDriver.lean').write_text(source[:start]+selected+source[end:])
expected={}
for src in ['evidence/ledger20-20261109/NKW_EXPECTED_IMPORTS.jsonl','evidence/tx2-resume2-20261109/NKU_EXPECTED_IMPORTS.jsonl']:
 for line in Path(src).read_text().splitlines():
  row=json.loads(line)
  if row['module'] in expected:assert expected[row['module']]==row['imports'],row['module']
  expected[row['module']]=row['imports']
for module in files+['NLE_COMBINED_IMPORT','NLE_Driver','NLE_ProofDriver']:
 expected[module]=re.findall(r'^import ([\w.]+)',(E/(module+'.lean')).read_text(),re.M)
(E/'NLE_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=k,imports=v))+'\n' for k,v in sorted(expected.items())))
print(json.dumps(dict(modules=len(files),roots=len(roots),groups=len(groups))))
