from pathlib import Path
import json,re,copy
E=Path(__file__).resolve().parent
mods=['PCG_SdkPda','PCG_ErrorLaws','PCG_AddressLaws','PCG_RequestCarrier','PCG_AddressRoots','PCG_CheckpointAddress','PCG_MasterAddress','PCG_ConversionLaws','PCG_OwnedTree','PCG_CanonicalLaws','PCG_PageLaws','PCG_MarkerCodec','PCG_DigestBridge','PCG_ReturnBridge','PCG_GlobalLaw','PCG_PackLaw','PCG_PackComposition','PCG_MarkerSeed']
(E/'PCG_COMBINED_IMPORT.lean').write_text('\n'.join('import '+m for m in ['RPx_Deployed','NLS_COMBINED_IMPORT','NLF_SdkBorrowLaw','PCE_COMBINED_IMPORT']+mods)+'\n')
roots=['AspisR1.RPx_Deployed.deployed']
for m in mods:
 s=(E/(m+'.lean')).read_text()
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 for t in re.findall(r'^#print axioms (\S+)',s,re.M):
  name=t if t.startswith(ns+'.') else ns+'.'+t
  if name not in roots:roots.append(name)
(E/'PCG_ROOTS.json').write_text(json.dumps(dict(roots=roots),indent=1)+'\n')
# One headline group and up to20 small helper roots per scope; no unchanged replay.
groups=[roots[:1]]+[roots[i:i+20] for i in range(1,len(roots),20)]
(E/'PCG_GROUPS.json').write_text(json.dumps(groups,indent=1)+'\n')
expected={x['module']:x['imports'] for x in map(json.loads,(E/'PCG_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for f in E.glob('PCG_*.lean'):
 m=f.name[:-5];imports=['Init']
 for line in f.read_text().splitlines():
  if line.startswith('import '):
   for x in line[7:].split():
    if x not in imports:imports.append(x)
 expected[m]=imports
(E/'PCG_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n' for m,v in sorted(expected.items())))
tasks=json.loads((E/'PCG_TASKS.json').read_text());tasks['PCG_L080']={'kind':'lean','target':'PCG_COMBINED_IMPORT'}
base=tasks['PCG_L010']
for n,mode in [(81,'scan')]+[(82+i,'roots'+str(i)) for i in range(len(groups))]:
 t=copy.deepcopy(base);t['target']=mode;t['command'][-1]=mode;t['collect']=['PCG_binary_'+mode+'.json']+(['PCG_LOADED_scan.jsonl'] if mode=='scan' else [])
 tasks[f'PCG_L{n:03}']=t
(E/'PCG_TASKS.json').write_text(json.dumps(tasks,indent=1)+'\n');print(str(len(roots))+' roots; '+str(len(groups))+' raw groups; combined source prepared')
