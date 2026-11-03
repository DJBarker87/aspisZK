"""Pin unchanged repository sources for every affected module, without building."""
from pathlib import Path
import hashlib,json,lzma,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent
scan=json.loads((E/'NER_SCAN.json').read_text())
mods={r['module']:r for r in map(json.loads,lzma.open(E/'NER_MANIFEST.jsonl.xz','rt'))}
tracked=subprocess.check_output(['git','ls-files'],cwd=R,text=True).splitlines()
paths=set(tracked);by_name={}
for p in tracked:
 if p.endswith('.lean'):by_name.setdefault(Path(p).stem,[]).append(p)
result=[]
for m in scan['rebuild_order']:
 candidates=[p for p in [f'lean/{m.replace(".","/")}.lean',f'docs/research/100bit-spend-path-20261013/lean/{m.replace(".","/")}.lean'] if p in paths]
 if not candidates:candidates=by_name.get(m.split('.')[-1],[])
 if len(candidates)!=1:
  result.append(dict(module=m,status='ambiguous_or_missing',candidates=candidates));continue
 p=candidates[0]
 source=(R/p).read_bytes() if (R/p).exists() else subprocess.check_output(['git','show','HEAD:'+p],cwd=R)
 result.append(dict(module=m,repository_source=p,source_sha256=hashlib.sha256(source).hexdigest(),source_bytes=len(source),cohort_imports=mods[m]['imports'],old_object_sha256=mods[m]['artifacts'][0]['sha256'],status='source_located'))
(E/'NER_REBUILD_PLAN.json').write_text(json.dumps(dict(required_modules=len(result),focused_budget=200,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),modules=result),indent=2)+'\n')
print(json.dumps(dict(required=len(result),located=sum(r['status']=='source_located' for r in result),unresolved=[r['module'] for r in result if r['status']!='source_located'])))
