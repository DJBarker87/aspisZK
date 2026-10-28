"""Fail-closed reached-source guards for structural transfers lacking a recovered
standalone checker. Reject changed complete pinned source before a reference law
can be transferred. A rejection is source-association failure, not value failure.
"""
from pathlib import Path
import json,lzma,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');O=D/'classify-closure-guards';O.mkdir(exist_ok=True)
plan=json.loads((D/'closure-guard-plan.json').read_text());sources=json.loads(lzma.open(D/'classify-source-capture/sources.json.xz').read())['files'];fs=json.loads(lzma.open(D/'classify-functions.json.xz').read());out=[]
for row in plan:
 checks=[]
 for f in row['functions']:
  r=fs[f];pair=r.get('source_evidence',{});check=dict(function=f,source_class=r['class'],source=pair)
  if not all(c in pair for c in ['evidence','deployed']):check['status']='UNRESOLVED';checks.append(check);continue
  for c,v in pair.items():
   src=sources[v['key']];b=Path(src['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==v['file_sha256'],src['path']
   # The AST item interval is pinned by the capture's lines plus its exact item hash.
   item=b''.join(b.splitlines(keepends=True)[v['line']-1:v['end_line']]).lstrip().rstrip(b'\n')
   assert hashlib.sha256(item).hexdigest()==v['item_sha256'],(f,c,'item interval not exact')
   check[c+'_item']=item.decode()
  a,b=pair['evidence'],pair['deployed']
  check['status']='SOURCE GATE DISAGREEMENT' if a['item_sha256']!=b['item_sha256'] else 'IDENTICAL ITEM; ENCLOSING IMPL STILL SUBJECT TO REVIEW'
  checks.append(check)
  if check['status']=='SOURCE GATE DISAGREEMENT':break
 result=dict(row=row['id'],checks=checks,status=checks[-1]['status'],original_checker_recovered=False,gate='First fail-closed source-association guard of the requested structural transfer: complete old pinned reached-source item must still match before applying its historical law.',meaning='Reject source-law transfer and stop this row. Not a demonstrated output/semantic/privacy failure; not a new full structural equivalence proof.')
 assert result['status']=='SOURCE GATE DISAGREEMENT',(row['id'],result)
 out.append(result);print(row['id'],result['status'],flush=True)
(O/'results.json').write_text(json.dumps(dict(results=out,policy='Native differentials already ran before these guard rejections; do not run/re-credit a rejected row after its stop.'),indent=2)+'\n')
