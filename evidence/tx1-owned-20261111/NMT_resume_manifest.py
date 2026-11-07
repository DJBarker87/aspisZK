"""Select only currently passing own sources and their printed theorem roots.
Preserve historical audit groups; no broad imported-root discovery."""
from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[json.loads(l)for l in (E/'NMT_ATTEMPTS.jsonl').read_text().splitlines()]
current={}
for r in rows:
 f=E/(r.get('module','')+'.lean')
 if r.get('kind')=='lean' and r.get('exit_status')==0 and f.is_file() and sha(f.read_bytes())in r['source_hashes'].values():current[r['module']]=r
new={m:r for m,r in current.items()if int(r['attempt'][5:])>60 and m!='NMT_RESUME_COMBINED_IMPORT'}
roots={}
for m,r in new.items():
 for l in r.get('print_axioms',[]):
  x=re.match("'([^']+)' (?:depends|does not depend)",l)
  if x:roots[x[1]]=m
assert roots and not any('sorryAx'in l for r in new.values()for l in r.get('print_axioms',[]))
# Check every new theorem is printed; copies of canonical proofs are printed
# together by NMT_RSL_Print. This checks names, not a library-wide root scan.
printed=set(n.split('.')[-1]for n in roots)
missing=[]
for m in new:
 for n in re.findall(r'^\s*(?:theorem|lemma)\s+([\w.]+)',(E/(m+'.lean')).read_text(),re.M):
  if n.split('.')[-1]not in printed:missing.append((m,n))
assert not missing,missing
result=dict(modules=list(current),new_modules=list(new),passing_sources={m:sha((E/(m+'.lean')).read_bytes())for m in current},new_roots=roots,policy='Only passing current source hashes; source support and copied canonical specs, no candidate credit')
(E/'NMT_RESUME_MODULES.json').write_text(json.dumps(result,indent=1)+'\n')
old=json.loads((E/'NMT_AUDIT_ROOTS.json').read_text());oldmods=json.loads((E/'NMT_AUDIT_MODULES.json').read_text())
groups=old['groups'][:2];modules=oldmods[:2]
names=list(roots)
for i in range(0,len(names),45):
 group=names[i:i+45];groups.append(group);modules.append(list(dict.fromkeys(roots[n]for n in group)))
(E/'NMT_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=groups),indent=1)+'\n')
(E/'NMT_AUDIT_MODULES.json').write_text(json.dumps(modules,indent=1)+'\n')
(E/'NMT_RESUME_COMBINED_IMPORT.lean').write_text('import NLX_COMBINED_IMPORT\n'+'\n'.join('import '+m for m in new)+'\n#print axioms NMT_345.source_fold\n#print axioms NMT_345PostObservation.suffix_packet\n#print axioms NMT_345.validated_public_domain\n')
print(json.dumps(dict(new_modules=len(new),new_roots=len(roots),audit_groups=len(groups)-2)))
