"""Conservative bc audit of fresh emitted definitions against pinned source spans."""
from pathlib import Path
import json,re,hashlib,lzma,base64
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
payload=json.loads(lzma.decompress((E/'NMP_FROZEN_PAYLOAD.json.xz').read_bytes()))
rows=[];routes=[]
for fn,n in [('prepare',2)]:
 out=E/'NMP_emitted'/fn;pins=json.loads((out/'NMP_PINS.json').read_text());assert pins['exit']==0 and pins['aeneas_exit']==0
 raw=out/'raw'/('NMP_'+fn)/'Funs.lean';s=raw.read_text()
 assert not re.search(r'\b(?:partial_fixpoint|loop|loop_invariant)\b',s),'Inspect generated loop manually'
 for m in re.finditer(r"/-- \[([^\]]+)\][\s\S]*?Source: '([^']+)', lines (\d+):\d+-(\d+):\d+[\s\S]*?-/(.*?)(?=\n/--|\nend NMP_|\Z)",s,re.S):
  name,file,start,end,body=m.groups()
  if file not in payload:
   rows.append(dict(function=fn,name=name,file=file,status='SDK_STD_BOUNDARY_NOT_USED_FOR_ROW_CREDIT',emitted_sha256=sha(body.encode())));continue
  source=base64.b64decode(payload[file]).decode();segment='\n'.join(source.splitlines()[int(start)-1:int(end)])
  clean=re.sub(r'//[^\n]*|/\*[\s\S]*?\*/','',segment)
  loops=bool(re.search(r'\b(?:while|for|loop)\b',clean))
  # Trait-impl headers contain "for"; this is not a source loop.
  loops=bool(re.search(r'\bwhile\b|\bloop\s*\{|\bfor\s+\w+\s+in\b',clean))
  assert not loops,(fn,name,'needs explicit review')
  rows.append(dict(function=fn,name=name,file=file,lines=[int(start),int(end)],source_sha256=sha(source.encode()),span_sha256=sha(segment.encode()),emitted_sha256=sha(body.encode()),status='NO_SOURCE_LOOP_NO_POST_LOOP_RETURN_PATTERN'))
 routes.append(dict(row='TX1:137+TX1:087',function=fn,attempt=f'NMP_E{n:03}',route='bm emitted actual body',exit=0,raw_funs_sha256=sha(raw.read_bytes()),pins=str((out/'NMP_PINS.json').relative_to(E)),qualification='Raw opaque templates excluded. Callee laws and representation transport still required; no candidate credit.'))
(E/'NMP_BC_AUDIT.json').write_text(json.dumps(dict(status='PASS_NO_POST_LOOP_PATTERN_IN_OWN_FRESH_BODIES',definitions=rows),indent=1)+'\n')
(E/'NMP_ROUTES.json').write_text(json.dumps(routes,indent=1)+'\n')
print(json.dumps(dict(routes=len(routes),definitions=len(rows),status='PASS')))
