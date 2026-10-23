#!/usr/bin/env python3
"""Enumerate source-level opaque functions; no automatic correctness attribution."""
from pathlib import Path
import hashlib,json,sys
receipt=json.loads(Path(sys.argv[3]).read_text()) if len(sys.argv)>3 else None
p=Path(sys.argv[1]);x=json.loads(p.read_text())['translated'];rows=[]
for f in x['fun_decls']:
 if not f or f.get('body')!='Opaque':continue
 name=f['item_meta']['name']
 span=f['item_meta'].get('span',{}).get('data',{})
 file=next((z for z in x['files'] if z['id']==span.get('file_id')),None)
 first=name[0].get('Ident',[''])[0]
 source_pin=None
 if first.startswith('aspis_'):
  fragment=f['item_meta'].get('source_text')
  if fragment is None and file and file.get('contents'):
   fragment=''.join(file['contents'].splitlines(keepends=True)[span['beg']['line']-1:span['end']['line']])
  if fragment is None and file and receipt:
   relative=file.get('name',{}).get('Local')
   if relative:
    candidate=p.parent/relative
    if candidate.is_file():
     data=candidate.read_bytes();digest=hashlib.sha256(data).hexdigest()
     matches=digest==receipt.get('source_sha256',{}).get(relative)
     source_pin=dict(path=relative,sha256=digest,matches_extraction_input=matches)
     if matches:fragment=''.join(data.decode().splitlines(keepends=True)[span['beg']['line']-1:span['end']['line']])
  rows.append(dict(source_pin=source_pin,id=f['def_id'],category='constant_initializer' if f.get('is_global_initializer') is not None else 'function',display_name='::'.join(z.get('Ident',['<impl>'])[0] for z in name),name=name,signature=f['signature'],source=f['item_meta'].get('span'),file=file['name'] if file else None,source_text=fragment,contract_status='Needs exact source/domain/contract mapping; opacity is not a correctness proof'))
result=dict(llbc_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),llbc_bytes=p.stat().st_size,opaque_project_functions=rows,count=len(rows),function_count=sum(r['category']=='function' for r in rows),constant_initializer_count=sum(r['category']=='constant_initializer' for r in rows),complete_contract_gate=False)
Path(sys.argv[2]).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(count=len(rows),function_count=sum(r['category']=='function' for r in rows),constant_initializer_count=sum(r['category']=='constant_initializer' for r in rows),complete_contract_gate=False)))
