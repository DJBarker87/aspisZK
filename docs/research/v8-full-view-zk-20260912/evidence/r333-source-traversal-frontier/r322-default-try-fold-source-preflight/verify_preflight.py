#!/usr/bin/env python3
"""Check saved source preflight facts only; never invokes the translator or build tools."""
from pathlib import Path
import hashlib,json
base=Path(__file__).resolve().parent
root=base.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=json.loads((root/'r294-private-norm-batch-extract/R294PrivateNormBatch.llbc').read_text())
b=json.loads((root/'r297-private-norm-batch-monomorphized/R297PrivateNormBatch.llbc').read_text())
assert a['has_errors'] is False and b['has_errors'] is False
f58=next(d for d in a['translated']['fun_decls'] if d and d['def_id']==58)
assert f58['item_meta']['opacity']=='Foreign' and f58['body']=='Opaque'
assert f58['item_meta']['name'][4]['Ident'][0]=='Iterator' and f58['item_meta']['name'][5]['Ident'][0]=='try_fold'
for i in [36,37,38,39,40]:
 d=next(d for d in b['translated']['fun_decls'] if d and d['def_id']==i)
 assert d['item_meta']['opacity']=='Foreign' and d['body']=='Opaque',i
assert len(json.loads((base/'source-rows-and-candidate-patterns.json').read_text())['candidate_include_patterns'])==4
print(json.dumps({'R294_Fun58':'Foreign/Opaque','R297_Funs_36_to_40':'Foreign/Opaque','candidate_patterns':4,'compilation_or_translation':False},indent=2))
