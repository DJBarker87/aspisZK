from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent
p=E/'NGJ_CONFLICTS.json';d=json.loads(p.read_text());v=json.loads(lzma.decompress((E/'NGJ_CLOSURE_PINS.json.xz').read_bytes()));q=json.loads(lzma.decompress((E/'NGJ_POOL_CLOSURE_PINS.json.xz').read_bytes()))
for r in d['conflicts']:
 r['canonical_loaded_objects']=[x for x in v['selected_objects'] if x['module']==r['canonical_owner']]
 r['Pool_original_loaded_objects']=[x for x in q['selected_objects'] if x['module']==r['original_owner']]
 assert r['canonical_loaded_objects'] and r['Pool_original_loaded_objects'] and r['verifier_import_path'] and r['Pool_import_path']
d['source_realization_boundary']='Module names, import-table paths and exact selected object/sidecar SHA256 are provenance. Source-to-object/library/compiler realization remains accepted tool trust, not re-proved here.'
p.write_text(json.dumps(d,indent=1)+'\n')
