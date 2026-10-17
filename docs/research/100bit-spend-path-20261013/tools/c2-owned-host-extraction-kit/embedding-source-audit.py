#!/usr/bin/env python3
"""Exact source/layout and raw generation audit for the independent primitive."""
from pathlib import Path
import argparse,hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[5];H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--revision',required=True);ap.add_argument('--translation',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--check',action='store_true');a=ap.parse_args()
 rev=subprocess.check_output(['git','-C',str(ROOT),'rev-parse',a.revision]).decode().strip();pins=json.loads((H/'input-embedding/source-pins.json').read_text());lib=(H/'input-embedding/lib.rs').read_bytes();assert sha(lib)==pins['kit_files']['lib.rs'];spans=[]
 for x in pins['cuts']:
  raw=subprocess.check_output(['git','-C',str(ROOT),'show',rev+':'+x['path']]);b=raw[x['start_byte']:x['end_byte_exclusive']];assert sha(b)==x['sha256'],x['name'];assert lib.count(b)==1,('No unique exact source fragment',x['name'])
  start=lib.index(b);end=start+len(b);spans.append({**x,'current_revision':rev,'current_source_file_sha256':sha(raw),'lib_start_byte':start,'lib_end_byte_exclusive':end,'lib_start_line':lib[:start].count(b'\n')+1,'lib_end_line':lib[:end].count(b'\n')+1,'classification':'unchanged source slice'})
 meta=json.loads(a.translation.read_text());mapped=[]
 for kind in ['functions','types','globals']:
  for x in meta.get(kind,[]):
   assert not x.get('is_opaque',False),x['lean_name']
   loc=x.get('source');assert loc and loc['file']=='lib.rs',x
   matches=[s for s in spans if s['lib_start_line']<=loc['begin_line'] and loc['end_line']<=s['lib_end_line']]
   if x['lean_name'].endswith('.embed_project_entry'):
    assert not matches
    status={'classification':'SYNTHETIC_ROOT_WRAPPER','original_source_declaration':None,'scope':'Only calls the actual constructor then actual c0; not a production Rust declaration.'}
   else:
    assert len(matches)==1,(x,matches)
    c=matches[0];status={'classification':'EXACT_ACTUAL_PRIMITIVE' if 'closure' not in x['lean_name'] else 'GENERATED_CLOSURE_FROM_EXACT_ENCLOSING_BODY','original_source_declaration':c['name'],'original_path':c['path'],'original_declaration_sha256':c['sha256']}
   mapped.append({'kind':kind,**x,**status})
 out={'source_revision':rev,'extraction_source_revision':pins['revision'],'lib_sha256':sha(lib),'raw_translation_sha256':sha(a.translation.read_bytes()),'selected_source_layout':spans,'emitted_declarations':mapped,'body_scope':'Only field embedding/canonicalization/projection. No actual Backend/build/transport/encode/custody acceptance. No source adaptation or new opaque boundary is reachable.','prior_boundary':'Prepared/tx1 models leave from_qm31 as explicit B.fromQm; this fresh namespace does not silently bind those prior models. No old generated body existed there to diff. Rust item bodies unchanged; current emitted statements and bodies are preserved raw.'}
 b=(json.dumps(out,indent=2,sort_keys=True)+'\n').encode()
 if a.check:assert a.out.read_bytes()==b
 else:a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_bytes(b)
 print(json.dumps({'check':a.check,'declarations':len(mapped),'layout_spans':len(spans),'audit_sha256':sha(b)}))
if __name__=='__main__':main()
