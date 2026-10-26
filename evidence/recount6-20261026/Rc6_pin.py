"""Read-only selected-source/object inventory; no build or launcher changes."""
from pathlib import Path
import json,subprocess,hashlib
P=Path(__file__).resolve().parent;R=P.parents[1]
paths=json.loads((P/'Rc6_005.json').read_text())['env']['LEAN_PATH'].split(':')
local={p.stem:hashlib.sha256(p.read_bytes()).hexdigest() for p in (R/'lean').glob('*.lean')}
roots=['Rc6_Top','Rc6_Statements','Rc6_Equivalent','Rc6_Nonvacuity','PFin_Packet','P6C_FullBoundary']
code='''from pathlib import Path
import json,hashlib
paths=PATHS
local=LOCAL
seen={}
def digest(p):return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def visit(m):
 if m in seen:return
 obj=next((Path(r)/(m.replace('.','/')+'.olean') for r in paths if (Path(r)/(m.replace('.','/')+'.olean')).is_file()),None)
 if obj is None:raise FileNotFoundError(m)
 item=dict(object=digest(obj));seen[m]=item
 for suffix in ['.private','.server']:
  q=Path(str(obj)+suffix)
  if q.is_file():item[suffix]=digest(q)
 src=obj.with_suffix('.lean')
 if not src.is_file():
  item['source_status']='object-only inherited cache; provenance in SInt2 manifests';return
 item['source']=digest(src)
 if m in local:item['matches_repository']=local[m]==item['source']['sha256']
 for line in src.read_text().splitlines():
  if line.startswith('import '):
   for n in line[7:].split():visit(n)
for m in ROOTS:visit(m)
print(json.dumps(seen,indent=2))
'''.replace('PATHS',repr(paths)).replace('LOCAL',repr(local)).replace('ROOTS',repr(roots))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True,check=True)
x=json.loads(r.stdout)
(P/'Rc6_selected_closure.json').write_text(json.dumps(x,indent=2)+'\n')
bad={k:v for k,v in x.items() if v.get('matches_repository') is False}
summary=dict(modules=len(x),source_compared=sum('matches_repository' in v for v in x.values()),mismatches=bad,object_only=sum('source' not in v for v in x.values()),note='Pinned focused closure with inherited caches; not a coherent frozen-release replay')
(P/'Rc6_source_check.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(dict(modules=summary['modules'],source_compared=summary['source_compared'],mismatches=list(bad),object_only=summary['object_only'])))
# The predecessor records these two documentation-only source variants.
import re,difflib
variants={}
for m,item in bad.items():
 remote=subprocess.check_output(['ssh','dombarker@100.108.41.90','cat '+item['source']['path']],text=True)
 current=(R/'lean'/(m+'.lean')).read_text()
 strip=lambda t:re.sub(r'/\-.*?\-/', '',t,flags=re.S)
 assert m in {'Op5T_Final','Op5T_SuccessAccepted'} and strip(remote)==strip(current),m
 variants[m]=dict(host_source_sha256=item['source']['sha256'],repository_source_sha256=local[m],identical_outside_comments=True,diff=''.join(difflib.unified_diff(remote.splitlines(True),current.splitlines(True),fromfile='host',tofile='repository')))
(P/'Rc6_comment_variants.json').write_text(json.dumps(variants,indent=2)+'\n')
summary['comment_only_variants']=list(variants)
summary['substantive_mismatches']=[]
(P/'Rc6_source_check.json').write_text(json.dumps(summary,indent=2)+'\n')
