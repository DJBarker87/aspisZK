#!/usr/bin/env python3
"""Check actual source identities and retain exact transparent/opaque boundary."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/verifier-top-20261023';x=json.loads((E/'aeneas-002/sources/VTop_Stages.llbc').read_text());assert not x['has_errors'];t=x['translated'];rows=[]
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
for d in t['fun_decls']:
 if d is None:continue
 m=d['item_meta'];source=m.get('source_text');span=m['span']['data'];file=t['files'][span['file_id']];path=file['name'].get('Local') if isinstance(file['name'],dict) else None
 if source and path and (R/path).is_file():
  # Charon's span is inclusive at start and exclusive at end, columns zero-based.
  lines=(R/path).read_text().splitlines(keepends=True);a=span['beg'];b=span['end'];cut=''.join(lines[a['line']-1:b['line']]);cut=cut[a['col']:];tail=len(lines[b['line']-1])-b['col'];cut=cut[:-tail] if tail else cut
  assert source==cut,(path,m['name'])
 else:cut=None
 rows.append({'name':m['name'],'path':path,'span':span,'source_sha256':sha(source) if source else None,'matches_worktree':cut==source if cut is not None else None,'transparent':isinstance(d.get('body'),dict) and 'Structured' in d['body']})
roots=[r for r in rows if r['transparent'] and not any(i.get('Ident',[None])[0]=='drop_glue' for i in r['name'])];assert len(roots)==3,roots
assert all(r['matches_worktree'] for r in roots)
(E/'source-identities.json').write_text(json.dumps({'llbc_sha256':hashlib.sha256((E/'aeneas-002/sources/VTop_Stages.llbc').read_bytes()).hexdigest(),'functions':rows,'qualification':'Exact span/source identity inspection, not an ELF proof or an instance of per-cone semantic refinement.'},indent=2)+'\n')
print(len(roots),'actual source bodies; all reached source-text spans checked')
