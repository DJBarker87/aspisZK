"""Generate new, unchanged-body import retargets from pinned historical sources."""
from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];L=R/'lean'
plan=json.loads((E/'NDO_RETARGET_PLAN.json').read_text());mapping=json.loads((E/'NDO_NAME_MAP.json').read_text());mapping.update({r['original']:r['module'] for r in plan});rows=[]
for row in plan:
 old=row['original'];p=Path('/tmp/NDO_originals')/(old.replace('.','/')+'.lean')
 if p.is_file():raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==row['source_sha256'],old
 else:
  p=L/(old.replace('.','/')+'.lean');raw=p.read_bytes()
 s=raw.decode()
 forbidden=re.findall(r'^\s*(?:axiom|opaque)\s|\b(?:sorry|admit|native_decide)\b',re.sub(r'/\-.*?\-/|--[^\n]*','',s,flags=re.S),re.M)
 assert not forbidden,(old,forbidden)
 def fix(m):return 'import '+' '.join(mapping.get(n,n) for n in m.group(1).split())
 t=re.sub(r'^import\s+([^\n]+)',fix,s,flags=re.M)
 # Only the requested root receives a new declaration namespace.
 if old=='JHx_Joint':t=t.replace('namespace AspisR1.JHx_Joint','namespace AspisR1.NDO_Joint').replace('end AspisR1.JHx_Joint','end AspisR1.NDO_Joint')
 dst=L/(row['module']+'.lean');dst.write_text(t)
 expected=re.sub(r'^import[^\n]*\n','',s,flags=re.M)
 actual=re.sub(r'^import[^\n]*\n','',t,flags=re.M)
 if old=='JHx_Joint':actual=actual.replace('AspisR1.NDO_Joint','AspisR1.JHx_Joint')
 assert expected==actual,old
 rows.append({**row,'path':str(dst.relative_to(R)),'historical_sha256':hashlib.sha256(raw).hexdigest(),'retarget_sha256':hashlib.sha256(t.encode()).hexdigest(),'non_import_bytes_unchanged':True,'historical_source_origin':row['source'] or str(p.relative_to(R))})
(E/'NDO_RETARGET_SOURCES.json').write_text(json.dumps(rows,indent=2)+'\n')
print(len(rows),'new modules; all non-import bytes unchanged (root namespace exception recorded)')
