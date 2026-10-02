#!/usr/bin/env python3
"""Verify saved source and LLBC hashes; decode R295's signature-failure rows."""
import hashlib, json, pathlib
HERE=pathlib.Path(__file__).resolve().parent
WORKTREE=HERE.parents[1]
EXPECTED={
 'SymbolicToPureTypes.ml':'29f4a784b0edb1dccf895aba78ec6d5c15c081e8602f7778db264b21272c54a0',
 'iterator.rs':'db43b7acc33fca53d85fef3ddea29ec9f8c1e768df428676fe2de160f21d5f6b',
}
for n,h in EXPECTED.items(): assert hashlib.sha256((HERE/n).read_bytes()).hexdigest()==h
llbc=WORKTREE/'.r21-scratch/r295-private-batch-translation/R294PrivateNormBatch.input.llbc'
assert hashlib.sha256(llbc.read_bytes()).hexdigest()=='bf5ea0b6f68ab17ef73d3e721c70c9193a0682d95dcbcaf693e93187cf71da6f'
d=json.loads(llbc.read_text()); assert d['has_errors'] is False
tr=d['translated']; f=next(x for x in tr['fun_decls'] if isinstance(x,dict) and x.get('def_id')==58)
assert f['item_meta']['span']['data']=={'file_id':19,'beg':{'line':2486,'col':4},'end':{'line':2490,'col':35}}
assert len(f['generics']['trait_type_constraints'])==1
assert f['generics']['trait_type_constraints'][0]['skip_binder']['type_id']==0
print('R295 signature inventory hashes/rows verified')
