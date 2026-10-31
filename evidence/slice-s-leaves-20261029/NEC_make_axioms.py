from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
rows=[json.loads(l) for l in (E/'NEC_ATTEMPTS.jsonl').read_text().splitlines()]
latest={}
for r in rows:
 if r['kind']=='lean' and r['exit_status']==0 and r['module']!='NEC_Axioms':latest[r['module']]=r
imports=[];theorems=[]
for module,r in latest.items():
 p=E/(module+'.lean')
 if not p.exists():continue
 expected=r['source_hashes']['NEC_generated/'+module+'.lean']
 assert hashlib.sha256(p.read_bytes()).hexdigest()==expected,('Changed proved module',module)
 imports.append(module.replace('/','.'))
 for line in r['print_axioms']:
  m=re.match("'([^']+)'",line)
  if m and m[1] not in theorems:theorems.append(m[1])
assert theorems
(E/'NEC_Axioms.lean').write_text(''.join('import '+m+'\n' for m in imports)+'\n'+''.join('#print axioms '+t+'\n' for t in theorems))
(E/'NEC_AXIOMS_TARGETS.json').write_text(json.dumps(dict(modules=imports,theorems=theorems,scope='Only latest accepted sources; failed drafts and metadata rejections excluded'),indent=1)+'\n')
print('Accepted imports',len(imports),'theorems',len(theorems))
