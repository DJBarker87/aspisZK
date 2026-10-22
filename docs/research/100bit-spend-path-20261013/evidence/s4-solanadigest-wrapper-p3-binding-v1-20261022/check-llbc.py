#!/usr/bin/env python3
"""Check focused emitted LLBC against the intended actual wrapper cut."""
import hashlib, json, sys
from pathlib import Path

p = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name('DigestWrapper-v4.llbc')
doc = json.loads(p.read_text())
assert doc.get('has_errors') is False, 'Charon reported LLBC errors'
t = doc['translated']
assert t['ordered_decls'], 'ordered_decls must be nonempty'

def path_name(meta):
    out=[]
    for x in meta['name']:
        if 'Ident' in x:
            out.append(x['Ident'][0])
        elif 'Impl' in x:
            out.append('<impl>')
    return '::'.join(out)

funs={x['def_id']:x for x in t['fun_decls']}
types={x['def_id']:x for x in t['type_decls']}
traits={x['def_id']:x for x in t['trait_decls']}
assert path_name(funs[0]['item_meta']) == 's4_solana_digest_wrapper_cut::digest_probe'
assert funs[0]['item_meta']['opacity'] == 'Transparent' and isinstance(funs[0]['body'],dict)
wrapper=next(x for x in t['fun_decls'] if x['item_meta'].get('source_text','').startswith('fn digest('))
assert wrapper['item_meta']['opacity']=='Transparent' and isinstance(wrapper['body'],dict)
assert 'hashv' in wrapper['item_meta']['source_text'] and 'to_bytes' in wrapper['item_meta']['source_text']
hashv=next(x for x in t['fun_decls'] if path_name(x['item_meta'])=='solana_sha256_hasher::hashv')
assert hashv['item_meta']['opacity']=='Opaque' and hashv['body']=='Opaque'
tobytes=next(x for x in t['fun_decls'] if path_name(x['item_meta']).startswith('solana_hash::<impl>::to_bytes'))
assert tobytes['item_meta']['opacity']=='Transparent' and isinstance(tobytes['body'],dict)
# Its MIR copies the single tuple/struct field from Hash and returns it.
tobody=json.dumps(tobytes['body'],sort_keys=True)
assert '"Copy"' in tobody and '"Field"' in tobody and '"Adt": [1, null]' in tobody
# Hash is transparent and exactly a one-field [u8; 32] representation.
hash_ty=next(x for x in t['type_decls'] if path_name(x['item_meta'])=='solana_hash::Hash')
assert hash_ty['item_meta']['opacity']=='Transparent'
hashkind=json.dumps(hash_ty['kind'],sort_keys=True)
assert "\"Array\"" in hashkind and "\"UInt\": \"U8\"" in hashkind and "\"Unsigned\": [\"Usize\", \"32\"]" in hashkind
# The actual SolanaDigest implementation of core::marker::Copy is emitted.
copy_trait=next(i for i,x in traits.items() if path_name(x['item_meta'])=='core::marker::Copy')
copy_impl=next(x for x in t['trait_impls'] if x.get('impl_trait',{}).get('id')==copy_trait and
                path_name(x['item_meta']).endswith('<impl>'))
assert copy_impl['item_meta']['opacity']=='Transparent'
# The intended nodes are in the ordered closure; the primitive itself is retained as opaque.
ordered=json.dumps(t['ordered_decls'])
for token in ('"Type": {"NonRec": 1}', '"Type": {"NonRec": 0}',
              '"Fun": {"NonRec": 3}', '"Fun": {"NonRec": 1}', '"Fun": {"NonRec": 0}'):
    assert token in ordered, f'missing ordered declaration {token}'
assert '"Fun": {"NonRec": 2}' in ordered, 'hashv call target declaration is reachable'
print(json.dumps({
 'llbc':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
 'has_errors':False,'ordered_decls':len(t['ordered_decls']),
 'fun_decls':len(t['fun_decls']),'type_decls':len(t['type_decls']),
 'transparent_wrapper':path_name(wrapper['item_meta']),
 'transparent_to_bytes':path_name(tobytes['item_meta']),
 'opaque_hashv':path_name(hashv['item_meta']),
 'hash_repr':'one field [u8; 32]','solana_digest_copy':True
},indent=2))
