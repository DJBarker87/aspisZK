"""Append own current-source roots to the raw ax2 manifest, one root per scope.
Smallest audits avoid retaining several large traversal graphs at once.
"""
from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent
accepted={}
for p in sorted(E.glob('LIBB_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());m=r['module'];s=E/(m+'.lean')
 if r['kind']=='lean' and r['exit_status']==0 and s.exists() and hashlib.sha256(s.read_bytes()).hexdigest() in r['source_hashes'].values():
  accepted[m]=r
rootfile=E/'LIBB_AUDIT_ROOTS.json';modfile=E/'LIBB_AUDIT_MODULES.json';indexfile=E/'LIBB_AUDIT_INDEX.json'
x=json.loads(rootfile.read_text())if rootfile.exists()else{'groups':[]}
mods=json.loads(modfile.read_text())if modfile.exists()else[]
idx=json.loads(indexfile.read_text())if indexfile.exists()else[]
known={r['root']:r['source_sha256']for r in idx}
for m,r in accepted.items():
 s=(E/(m+'.lean')).read_text();sha=hashlib.sha256(s.encode()).hexdigest()
 ns=re.search(r'^namespace ([\w.]+)',s,re.M)
 if not ns:continue
 for local in re.findall(r'^#print axioms ([\w.]+)',s,re.M):
  root=local if local.startswith('LIBB_')else ns[1]+'.'+local
  if root in known:
   assert known[root]==sha,('Root source changed after audit scheduling',root)
   continue
  n=len(x['groups']);x['groups'].append([root]);mods.append([m]);idx.append(dict(group=n,root=root,module=m,source_sha256=sha,compile_attempt=r['attempt']))
  known[root]=sha
rootfile.write_text(json.dumps(x,indent=1)+'\n');modfile.write_text(json.dumps(mods,indent=1)+'\n');indexfile.write_text(json.dumps(idx,indent=1)+'\n')
print(json.dumps(dict(accepted_modules=len(accepted),audit_groups=len(x['groups']))))
