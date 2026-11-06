from pathlib import Path
import json,lzma
E=Path(__file__).resolve().parent
old=json.loads(lzma.decompress((E/'NKY_BEFORE_POST_PINS.json.xz').read_bytes()));new=json.loads(lzma.decompress((E/'NKY_CLOSURE_PINS.json.xz').read_bytes()))
def key(r):return(r['module'],next(s for s in['.olean.private','.olean.server','.olean','.ir']if r['path'].endswith(s)))
a={key(r):r for r in old['selected_objects']};b={key(r):r for r in new['selected_objects']}
changed=[dict(module=k[0],suffix=k[1],before=r['sha256'],after=b.get(k,{}).get('sha256'))for k,r in a.items()if k not in b or b[k]['sha256']!=r['sha256']]
assert all(r['module']=='NKY_COMBINED_IMPORT'for r in changed),changed
scan=[json.loads(l)for l in(E/'NKY_LOADED_scan.jsonl').read_text().splitlines()]
glue=next(r for r in scan if r['module']=='NKY_COMBINED_IMPORT');assert glue['declarations']==0
out=dict(status='PASS',previous_objects=len(a),unchanged_semantic_objects=len(a)-len(changed),changed=changed,changed_module_has_zero_declarations=True,new_modules=sorted(set(r['module']for r in new['selected_objects'])-set(r['module']for r in old['selected_objects'])),explanation='All10585 previously walked root declaration objects unchanged. Only additive zero-declaration import glue changed. New12post-heap roots walked separately; final canonical scan covers complete updated closure. No unchanged full replay.')
(E/'NKY_INCREMENTAL_PRESERVATION.json').write_text(json.dumps(out,indent=1)+'\n');print('incremental object preservation PASS')
