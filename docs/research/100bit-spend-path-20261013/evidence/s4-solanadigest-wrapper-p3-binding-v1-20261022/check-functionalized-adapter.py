#!/usr/bin/env python3
"""Check the functionalized Lean body is the emitted method with only hashv freed."""
from pathlib import Path
import hashlib, json, re
root=Path(__file__).resolve().parent
funs=(root/'generated/AspisR1SolanaDigestWrapperCut/Funs.lean').read_text()
adapter=(root/'sources/S4SolanaDigestWrapperP3BindingV1.lean').read_text()
llbc=json.loads((root/'generated/DigestWrapper-v4.llbc').read_text())['translated']

def block(text, needle):
    start=text.index(needle)
    end=text.find('/--',start+len(needle))
    return text[start:] if end<0 else text[start:end]

emitted=block(funs,'def SolanaDigest.Insts.Aspis_coreDigestDigest32.digest')
functional=block(adapter,'def digest_with_hashv')

def rhs(text):
    m=re.search(r':= do\n(.*?)(?=\n(?:/--|def |end |$))',text,re.S)
    assert m, 'could not isolate do-body'
    return m.group(1).rstrip()

old=rhs(emitted)
new=rhs(functional)
old_callee='solana_sha256_hasher.hashv parts'
new_callee='hashv parts'
assert old.count(old_callee)==1, 'emitted method must call hashv exactly once'
assert old.replace(old_callee,new_callee)==new, 'adapter body must differ only by explicit hashv callee parameter'

tobytes=block(funs,'def solana_hash.Hash.to_bytes')
tobytes_adapter=block(adapter,'def solana_hash.Hash.to_bytes')
assert rhs(tobytes)==rhs(tobytes_adapter), 'Hash::to_bytes adapter body differs from emitted function'
assert 'let h ← hashv parts' in new and 'solana_hash.Hash.to_bytes h' in new
assert 'FunsExternal_Template' not in adapter and 'AspisR1SolanaDigestWrapperCut.Funs' not in adapter
assert not re.search(r'^\s*(?:axiom|sorry|admit)\b', adapter, re.M), 'adapter contains an admitted declaration'
wrapper=next(x for x in llbc['fun_decls'] if x['item_meta'].get('source_text','').startswith('fn digest('))
assert wrapper['item_meta']['opacity']=='Transparent'
assert 'hashv(parts).to_bytes()' in wrapper['item_meta']['source_text']
copy=next(x for x in llbc['trait_impls'] if x['def_id']==1)
assert copy['item_meta']['opacity']=='Transparent'
print(json.dumps({
 'emitted_funs_sha256':hashlib.sha256(funs.encode()).hexdigest(),
 'functionalized_adapter_sha256':hashlib.sha256(adapter.encode()).hexdigest(),
 'llbc_sha256':hashlib.sha256((root/'generated/DigestWrapper-v4.llbc').read_bytes()).hexdigest(),
 'digest_body_change':'exact single callee substitution: solana_sha256_hasher.hashv parts -> hashv parts',
 'to_bytes_body':'exact emitted body retained',
 'LLBC_method_opacity':wrapper['item_meta']['opacity'],
 'LLBC_Copy_impl_opacity':copy['item_meta']['opacity'],
 'status':'PASS'
},indent=2))
