from pathlib import Path
import json,re
E=Path(__file__).resolve().parent
mods=['NGL_CloneDomain','NGL_ReadonlyModel','NGL_FirstDecoded','NGL_CheckpointModel','NGL_LengthCarrier','NGL_SnapshotModel','NGL_SnapshotDomains','NGL_EntryRouting','NGL_ArrayEquality','NGL_ErrorCarrier','NGL_MetaReferenceModel','NGL_MapReferenceModel','NGL_SnapshotCases','NGL_HelperFrames','NGL_ErrorModel','NGL_ArrayPrimitives','NGL_DistinctStep','NGL_DistinctInduction','NGL_StorageCases','NGL_BorrowFrame','NGL_AuthGuards']
roots=['AspisR1.RPx_Deployed.deployed']
for m in mods:
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',s,re.M).group(1)
 roots.extend(ns+'.'+n for n in re.findall(r'#print axioms (\S+)',s))
(E/'NGL_AUDIT_ROOTS.json').write_text(json.dumps({'roots':roots,'groups':json.loads((E/'NGL_AUDIT_ROOTS_BASE.json').read_text())['groups']+[roots[52:]]},indent=1)+'\n')
(E/'NGL_COMBINED_IMPORT.lean').write_text('import NGJ_VERIFIER_IMPORT\n'+''.join('import '+m+'\n' for m in mods)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
rows=[json.loads(x) for x in (E.parent/'ledger8-20261105/NGJ_EXPECTED_IMPORTS.jsonl').read_text().splitlines()]
by={r['module']:r for r in rows}
for r in json.loads((E/'NGL_ROUTING_IMPORT_SOURCE_PINS.json').read_text())['modules']:
 if r['module'] not in by:
  item={'module':r['module'],'imports':r['imports']};rows.append(item);by[r['module']]=item
inputs=json.loads((E/'NGL_GENERATED_INPUTS.json').read_text())
for m in mods+['NGL_COMBINED_IMPORT']+list(inputs):
 p=E/inputs[m] if m in inputs else E/(m+'.lean');s=p.read_text();imports=['Init']
 for line in s.splitlines():
  if line.startswith('import '):imports.extend(x for x in line[7:].split() if x!='all')
 imports=list(dict.fromkeys(imports));r={'module':m,'imports':imports}
 if m in by:assert r==by[m]
 else:rows.append(r);by[m]=r
(E/'NGL_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
print(json.dumps({'new_modules':len(mods),'raw_roots':len(roots),'groups':len(json.loads((E/'NGL_AUDIT_ROOTS.json').read_text())['groups'])}))
