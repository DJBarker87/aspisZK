#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
base=Path(__file__).resolve().parent
orig_f=base/'Funs-original.lean'; new_f=base/'Funs-narrow.lean'
orig_t=base/'Types-original.lean';new_t=base/'Types-narrow.lean'
def body(p):return [x for x in p.read_text().splitlines() if not x.lstrip().startswith('import ') and not x.lstrip().startswith('open ')]
assert body(orig_f)==body(new_f), 'Funs non-import lines differ'
assert body(orig_t)==body(new_t), 'Types non-import lines differ'
assert orig_f.read_text().count('import Aeneas\n')==1
assert 'import Aeneas\n' not in new_f.read_text()
assert new_t.read_text().count('import Aeneas.Std.Scalar.Core\n')==1
print(json.dumps({'result':'PASS','original_funs_sha256':hashlib.sha256(orig_f.read_bytes()).hexdigest(),'adapted_funs_sha256':hashlib.sha256(new_f.read_bytes()).hexdigest(),'original_types_sha256':hashlib.sha256(orig_t.read_bytes()).hexdigest(),'adapted_types_sha256':hashlib.sha256(new_t.read_bytes()).hexdigest(),'comparison':'all non-import/open body lines are byte-for-byte equal; only import/open closure narrowed','funs_imports': [x for x in new_f.read_text().splitlines() if x.startswith('import ')],'types_imports':[x for x in new_t.read_text().splitlines() if x.startswith('import ')]},indent=2))
