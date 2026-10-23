#!/usr/bin/env python3
"""Concatenate exact emitted types/bodies; remove generated resource settings.
No operation, literal, branch, type field or callee replacement is performed.
"""
from pathlib import Path
import sys,json,hashlib,re
I=Path(sys.argv[1]);O=Path(sys.argv[2]);O.mkdir(parents=True,exist_ok=True);N='AspisS1M31Embedding'
t=(I/'Types.lean').read_text();f=(I/'Funs.lean').read_text();extract=lambda s:s.split('namespace '+N+'\n',1)[1].rsplit('end '+N,1)[0]
assert 'FunsExternal' not in f and 'TypesExternal' not in t
out='import Aeneas\nset_option autoImplicit false\nopen Aeneas Aeneas.Std Result ControlFlow Error\nnamespace '+N+'\n'+extract(t)+extract(f)+'\n#print axioms source_from_m31\nend '+N+'\n'
assert not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|maxRecDepth)\b',out.replace('#print axioms',''))
(O/'S1M31EmbeddingSourceV1.lean').write_text(out)
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
(O/'s1-m31-embedding-adapter.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',types_sha256=sha(t),funs_sha256=sha(f),source_sha256=sha(out),qualification=__doc__,removed='Only generated imports/options/noncomputable declaration wrapper; namespace bodies concatenated literally. No generated external axioms imported.'),indent=2)+'\n')
