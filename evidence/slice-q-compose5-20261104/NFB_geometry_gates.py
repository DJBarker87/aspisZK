"""Checked component receipts; root promotion additionally requires composition."""
from pathlib import Path
import sys,json,hashlib
from NFB_native_checks import pair,copy_group,native,obj
E=Path(__file__).resolve().parent
PAIRS=[(2,3,4,5,6,7),(8,9),(10,11),(15,16),(17,18,19,20,21),(22,23,24,25,26),
(29,30,31,32),(33,34,35,36),(37,38,39,40),(43,44),(47,48,49,50),(51,52,53,54),
(57,58,59,60,61),(62,63,64,65,66),(72,73,74,75),(76,77,78,79),
(80,81,82),(83,84,85),(86,87,88,89),(90,91,92,93),(96,97),(98,99,100),(101,102,103),(104,105,106)]
COPY=[(13,14),(27,28),(41,42),(45,46),(55,56),(67,68),(94,95),(107,108)]
name=lambda n:f'NFB_K{n:03}'
def check():
 pairs=[pair(*(name(n) for n in p)) for p in PAIRS]
 copies=[]
 for c,b in COPY:
  chosen=[p['positive']['attempt'] for p in pairs if p['positive']['source_hashes']==native(name(c),0)['source_hashes']]
  assert chosen,(c,'orphan copy configuration')
  copies.append(copy_group(name(c),name(b),chosen))
 covered={a for c in copies for a in c['targets']}
 for p in pairs:
  # This sole harness has only bool/usize locals: no slice/array/Vec or copy.
  assert p['positive']['attempt'] in covered or p['positive']['attempt']=='NFB_K096'
 sys.path.insert(0,str(E.parent/'slice-q-compose4-20261104'))
 import NEW_geometry_checks as prior
 inherited=obj(E.parent/'slice-q-compose4-20261104/NEW_NATIVE_PARTIAL_AUDIT.json')
 needed={41,43,45,48,51,60,62,68,71,73,81,84}
 old=[]
 for p in inherited['pairs']:
  if int(p['positive']['attempt'][-3:]) not in needed:continue
  old.append(prior.pair(p['positive']['attempt'],*(c['attempt'] for c in p['controls'])))
 assert len(old)==len(needed)
 for c,targets in inherited['copy_groups']:
  chosen=[p['positive']['attempt'] for p in old if p['positive']['attempt'] in targets]
  if not chosen:continue
  matching=next(p for p in inherited['pairs'] if p['positive']['attempt']==c)
  cp=prior.pair(c,*(b['attempt'] for b in matching['controls']))
  for a in chosen:
   assert cp['positive']['source_hashes']==prior.native(a,0)['source_hashes']
 return dict(pairs=pairs,copy_groups=copies,inherited_pairs=old,
  full_root_credit=False,reason='Components only; same-buffer/root/child association is separately required',
  suspended=[],quarantined=[],excluded=['K001 compiler error','K012 timeout','K069/K070 compiler ICE','K071 unwind failure'])
if __name__=='__main__':print(json.dumps(check(),indent=1))
