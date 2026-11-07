"""Select only successful CURRENT source owners; audit each new printed root once."""
from pathlib import Path
import json,hashlib,lzma,re,math
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[json.loads(l) for l in (E/'NMX_ATTEMPTS.jsonl').read_text().splitlines()]
exclude={'NMX_COMBINED_IMPORT','NMX_ProofDriver','NMX_ScanDriver','NMX_InspectByte','NMX_InspectLE','NMX_LEApi','NMX_UIntApi'}
exclude.update(p.stem for p in E.glob('NMX_RSL_*.lean'))
accepted={}
for r in rows:
 if r.get('kind')!='lean' or r.get('exit_status')!=0:continue
 m=r['module'];p=E/(m+'.lean')
 if m in exclude or not p.is_file():continue
 if sha(p)!=r['source_hashes'].get('NMX_generated/'+m+'.lean'):continue
 if m not in accepted or int(r['attempt'][-3:])>int(accepted[m]['attempt'][-3:]):accepted[m]=r
for m in accepted:
 for dep in re.findall(r'^import (NMX_[\w.]+)',(E/(m+'.lean')).read_text(),re.M):assert dep in accepted,(m,dep)
oldp=E/'NMX_AUDIT_ROOTS_BASELINE.json';oldm=E/'NMX_AUDIT_MODULES_BASELINE.json'
if not oldp.exists():oldp.write_bytes((E/'NMX_AUDIT_ROOTS.json').read_bytes())
if not oldm.exists():oldm.write_bytes((E/'NMX_AUDIT_MODULES.json').read_bytes())
base=json.loads(oldp.read_text());modules=json.loads(oldm.read_text());oldroots={r['root'] for r in base['records']};new={}
for m,r in accepted.items():
 raw=lzma.decompress((E/r['attempt']/'stdout.log.xz').read_bytes()).decode()
 for root in re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",raw):
  if root not in oldroots:
   assert root.startswith('NMX_'),(m,root)
   new[root]=m
newrows=[dict(root=r,module=m) for r,m in sorted(new.items())]
formal_count=sum(r.get('kind') in ['lean','link','audit','inspect'] for r in rows)
# Each new root is audited exactly once; no baseline audit is rerun.
# Leave precisely the combined import and retention scope for finalization.
combined=E/'NMX_COMBINED_IMPORT.lean'
combined_green=combined.is_file() and any(r.get('module')=='NMX_COMBINED_IMPORT' and r.get('exit_status')==0 and sha(combined) in r.get('source_hashes',{}).values() for r in rows)
remaining_groups=(289 if combined_green else 288)-formal_count
assert 1<=remaining_groups<=len(newrows)
for group_index in range(remaining_groups):
 start=group_index*len(newrows)//remaining_groups
 end=(group_index+1)*len(newrows)//remaining_groups
 group=newrows[start:end];base['groups'].append([r['root'] for r in group]);modules.append(sorted({r['module'] for r in group}))
base['records']+=newrows;base['renewal_first_group']=4
(E/'NMX_AUDIT_ROOTS.json').write_text(json.dumps(base,indent=1)+'\n');(E/'NMX_AUDIT_MODULES.json').write_text(json.dumps(modules,indent=1)+'\n')
mods=sorted(accepted)
(E/'NMX_EXPORT_MODULES.json').write_text(json.dumps(mods+['NMX_COMBINED_IMPORT'],indent=1)+'\n')
s='import NLX_COMBINED_IMPORT\n'+'\n'.join('import '+m for m in mods)+'\n'
for root in ['NMX_CutValueBridge.source','NMX_RSL233Fold.fold','NMX_SemanticF04.e041','NMX_NecessaryConditions.getter_stop_excluded','NMX_SevenSourceFold.fold']:
 s+='#print axioms '+root+'\n'
(E/'NMX_COMBINED_IMPORT.lean').write_text(s)
(E/'NMX_ACCEPTED_SOURCES.json').write_text(json.dumps({m:dict(attempt=r['attempt'],source_sha256=sha(E/(m+'.lean'))) for m,r in accepted.items()},indent=1)+'\n')
print(json.dumps(dict(modules=len(mods),new_roots=len(newrows),new_groups=len(base['groups'])-4)))
