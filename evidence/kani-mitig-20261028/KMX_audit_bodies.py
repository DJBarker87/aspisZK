from pathlib import Path
import json,re
E=Path(__file__).resolve().parent
sources=json.loads((E/'KMX_source_snapshots.json').read_text())['sources']
plan=json.loads((E/'KMX_ALL_REPLAY_PLAN.json').read_text())
rename=lambda s:re.sub(r'\b((?:LP[a-t]|NB[A-M])_\w*)',r'KMX_\1',s).replace('aspis_r1_cost_probe::','crate::')
rows=[]
for p in plan:
 original=sources[p['source_sha256']]['text'];current=(E/(p['module']+'.rs.txt')).read_text();name=p['original_harness'].split('::')[-1]
 m=re.search(r'fn\s+'+re.escape(name)+r'\s*\(',original)
 if m:
  i=original.index('{',m.end());depth=1;j=i+1
  while depth:
   depth+=(original[j]=='{')-(original[j]=='}');j+=1
  body=original[i:j];ok=rename(body) in current
 else:
  m=re.search(r'\w+!\('+name+r'[,)]',original);assert m,p
  i=m.start();depth=1;j=original.index('(',i)+1
  while depth:
   depth+=(original[j]=='(')-(original[j]==')');j+=1
  body=original[i:j];ok=rename(body) in current
 rows.append(dict(original=p['original'],body_unchanged_except_namespace=ok))
 assert ok,p
(E/'KMX_REPLAY_BODY_AUDIT.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Selected property bodies unchanged:',len(rows))
