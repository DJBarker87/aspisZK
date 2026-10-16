#!/usr/bin/env python3
"""Pin emitted inventory and actual roots; does not prove builtin semantics."""
from pathlib import Path
import argparse,hashlib,json,re
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--llbc',type=Path,required=True)
 ap.add_argument('--generated',type=Path,required=True);ap.add_argument('--kit',type=Path,required=True)
 ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 d=json.loads(a.llbc.read_text());t=d['translated'];assert not d['has_errors']
 lib=(a.kit/'lib.rs').read_bytes();assert t['files'][0]['contents'].encode()==lib
 pins=json.loads((a.kit/'source-pins.json').read_text())
 for name,h in pins['kit_files'].items():assert sha((a.kit/name).read_bytes())==h
 roots=[];opaque=[]
 for f in t['fun_decls']:
  if not f:continue
  meta=f['item_meta'];last=meta['name'][-1].get('Ident',[''])[0]
  if last in ['semantic_public','public_transcript']:
   assert isinstance(f['body'],dict) and meta['opacity']=='Transparent'
   assert meta['source_text'] in lib.decode()
   roots.append({'id':f['def_id'],'name':meta['name'],'source_text_sha256':sha(meta['source_text'].encode()),'span':meta['span']})
  if f['body']=='Opaque':
   opaque.append({'id':f['def_id'],'name':meta['name'],'is_local':meta['is_local'],'span':meta['span']})
 assert len(roots)==2
 tr=json.loads((a.generated/'translation.json').read_text())
 assert tr['aeneas_version']=='b59d5188c082f704a418c7cb4e52ad69328002d1'
 names=[x['lean_name'] for x in tr['functions']]
 assert any(x.endswith('.semantic_public') for x in names)
 assert any(x.endswith('.public_transcript') for x in names)
 assert all(not x['is_opaque'] for x in tr['functions'])
 files={str(p.relative_to(a.generated)):sha(p.read_bytes()) for p in a.generated.rglob('*') if p.is_file()}
 assert set(files)=={'AspisR1PublicPreparation/Types.lean','AspisR1PublicPreparation/Funs.lean','translation.json'}
 lean=(a.generated/'AspisR1PublicPreparation/Funs.lean').read_text()
 assert not re.search(r'^\s*(?:axiom|opaque|sorry)\b',lean,re.M)
 domain=lean.split('def r1_wire.DOMAIN :',1)[1].split('/--',1)[0]
 values=bytes(int(x) for x in re.findall(r'\b(\d+)#u8',domain))
 assert values==b'UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3'
 sources=[]
 for f in t['files']:
  sources.append({'id':f['id'],'name':f['name'],'crate':f['crate_name'],'contents_sha256':sha(f['contents'].encode()) if f.get('contents') is not None else None})
 result={'revision':pins['revision'],'llbc_sha256':sha(a.llbc.read_bytes()),'emitted_files':files,'actual_roots':roots,'domain_bytes_hex':values.hex(),
  'llbc_function_declarations':sum(x is not None for x in t['fun_decls']),'llbc_opaque_functions':opaque,'emitted_function_inventory':tr['functions'],'rust_file_inventory':sources,
  'generated_external_templates':[],'generated_opaque_functions':[],
  'builtin_boundary':'LLBC opaque records are retained explicitly; no template was emitted. Existing Aeneas backend models for Vec, scalar conversion, slices, iteration, Try and numeric bytes are imported, not proved equivalent to Rust here. Digest32.digest is an explicit dictionary parameter returning Result, including failure/divergence.',
  'excluded_claims':'Derived Debug definitions reference backend Formatter; no standard-only claim is made for those definitions or the whole module. Actual roots require separate Lean audits. No source/runtime/custody or outer first/tx1/verify_observed reachability theorem.'}
 a.out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'actual_roots':len(roots),'emitted_functions':len(tr['functions']),'llbc_opaque_functions':len(opaque),'generated_externals':0,'source_files':len(sources),'audit_sha256':sha(a.out.read_bytes())}))
if __name__=='__main__':main()
