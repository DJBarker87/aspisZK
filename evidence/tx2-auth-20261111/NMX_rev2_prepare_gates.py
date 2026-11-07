"""Select current accepted sources; audit only previously unaudited own roots."""
from pathlib import Path
import json,hashlib,lzma,re
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[json.loads(l) for l in (E/'NMX_ATTEMPTS.jsonl').read_text().splitlines()]
old=json.loads((E/'NMX_AUDIT_ROOTS.json').read_text());oldroots={r['root'] for r in old['records']}
accepted={}
for r in rows:
 m=r.get('module','');p=E/(m+'.lean')
 if not (m.startswith('NMX_R2_') or m=='NMX_LengthCloneCut') or r.get('kind')!='lean' or r.get('exit_status')!=0 or not p.is_file():continue
 if sha(p)!=r['source_hashes'].get('NMX_generated/'+m+'.lean'):continue
 accepted[m]=r
roots={}
for m,r in accepted.items():
 output=lzma.decompress((E/r['attempt']/'stdout.log.xz').read_bytes()).decode()
 for root in re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",output):
  if root not in oldroots:roots[root]=m
for m in accepted:
 for dep in re.findall(r'^import (NMX_R2_\w+|NMX_LengthCloneCut)',(E/(m+'.lean')).read_text(),re.M):assert dep in accepted,(m,dep)
records=[dict(root=root,module=m) for root,m in sorted(roots.items())]
groups=[records[:len(records)//2],records[len(records)//2:]]
(E/'NMX_REV2_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=old['groups']+[[r['root'] for r in g] for g in groups],records=records,first_new_group=len(old['groups'])),indent=1)+'\n')
(E/'NMX_REV2_AUDIT_MODULES.json').write_text(json.dumps(json.loads((E/'NMX_AUDIT_MODULES.json').read_text())+[sorted({r['module'] for r in g}) for g in groups],indent=1)+'\n')
(E/'NMX_REV2_ACCEPTED.json').write_text(json.dumps({m:dict(attempt=r['attempt'],source_sha256=sha(E/(m+'.lean'))) for m,r in accepted.items()},indent=1)+'\n')
s='import NLX_COMBINED_IMPORT\n'+'\n'.join('import '+m for m in sorted(accepted))+'\n'
for root in ['NMX_R2_NativeCanonical.fold','NMX_R2_RSL233Fold.fold','NMX_R2_ClonePacket.data','NMX_R2_CheckpointPacket.packet','NMX_R2_DistinctNative.packet','NMX_R2_ArgsInjection.injective']:
 if root in roots:s+='#print axioms '+root+'\n'
(E/'NMX_R2_COMBINED_IMPORT.lean').write_text(s)
print(json.dumps(dict(modules=len(accepted),new_roots=len(roots),audit_groups=2)))
