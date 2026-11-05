from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-entry6-20261107'
mods=['NIV_ReplyCuts','NIV_SnapshotSequence','NIV_OwnedPrefixes','NIV_SnapshotDomain','NIV_FrameWindows','NIV_SnapshotWrite','NIV_SdkFields','NIV_ExtractedForward','NIV_ForwardPacket']
(E/'NIV_COMBINED_IMPORT.lean').write_text('import NIS_COMBINED_IMPORT\nimport NGK_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in mods)+'\n#print axioms AspisR1.RPx_Deployed.deployed\n')
for m in ['ProofDriver','ScanDriver']:
 s=(P/('NIS_'+m+'.lean')).read_text().replace('NIS_','NIV_');(E/('NIV_'+m+'.lean')).write_text(s)
(E/'NIV_audit_one.py').write_text((P/'NIS_audit_one.py').read_text().replace('NIS_','NIV_'))
ats=list(map(json.loads,(E/'NIV_ATTEMPTS.jsonl').read_text().splitlines()));roots=['AspisR1.RPx_Deployed.deployed']
for m in mods:
 h=hashlib.sha256((E/(m+'.lean')).read_bytes()).hexdigest();rs=[r for r in ats if r['module']==m and r['exit_status']==0 and h in r['source_hashes'].values()];assert rs,m
 for line in rs[-1]['print_axioms']:
  root=re.match("'([^']+)'",line)[1]
  if root not in roots:roots.append(root)
(E/'NIV_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots]),indent=1)+'\n')
lines={x['module']:x for x in map(json.loads,(P/'NIS_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for m in mods+['NIV_COMBINED_IMPORT']:
 lines[m]=dict(module=m,imports=['Init']+re.findall(r'^import ([\w.]+)',(E/(m+'.lean')).read_text(),re.M))
(E/'NIV_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(lines[k])+'\n' for k in sorted(lines)))
print(json.dumps(dict(modules=len(mods),roots=len(roots))))
