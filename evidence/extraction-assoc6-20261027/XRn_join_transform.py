"""Reproducible name-only release-kit transform; no extraction or body edit."""
from pathlib import Path
import json,sys,hashlib
E=Path(__file__).resolve().parent
root=E.parent.parent
for item in json.loads((E/'XRn_join_plan.json').read_text()):
 source=(root/item['original']).read_text()
 assert hashlib.sha256(source.encode()).hexdigest()==item['source_sha256']
 expected=source.replace('XRk_','XRn_Join_')
 if item['module']=='XRn_Join_Types':
  expected=expected.replace('import Aeneas\n','import Aeneas\nimport ImportUnionNamedDiscriminant\n',1)
  expected=expected.replace('@[discriminant isize','@[import_union_discriminant')
 assert hashlib.sha256(expected.encode()).hexdigest()==item['sha256']
 path=E/(item['module']+'.lean')
 if '--check' in sys.argv:assert path.read_text()==expected,path
 else:path.write_text(expected)
print('17 exact name-only transforms checked')
