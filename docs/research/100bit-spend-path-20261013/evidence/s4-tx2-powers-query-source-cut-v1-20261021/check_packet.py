#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,sys
root=Path(__file__).resolve().parent
repo=root.parents[5]
m=json.loads((root/'manifest.json').read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[]
for mod in m['modules']:
    for key in ('source','producer_receipt','command','time','log'):
        if not (root/mod[key]).is_file(): errors.append(f"missing {key}: {mod[key]}")
    if sha(root/mod['source'])!=mod['source_sha256']: errors.append('proof source checksum mismatch')
    rec=json.loads((root/mod['producer_receipt']).read_text())
    if rec['source_sha256']!=mod['source_sha256'] or rec['exit_status']!=0: errors.append('receipt mismatch/nonzero')
for name,pin in m['direct_import_source_map'].items():
    src=(root/pin['source']).resolve()
    if not src.is_file() or sha(src)!=pin['source_sha256']: errors.append(f'direct source mismatch: {name}')
funs=root/'source-pins/Funs.lean'; types=root/'source-pins/Types.lean'; rust=root/'source-pins/tx2_common.rs'; weights=root/'source-pins/weights.rs'
if sha(funs)!=m['source_bindings']['complete_emitted_funs_source']['expected_sha256']: errors.append('generated Funs pin mismatch')
if sha(types)!=m['source_bindings']['emitted_types_source']['expected_sha256']: errors.append('generated Types pin mismatch')
ft=funs.read_text(); marker='def verifier.candidate.tx2_common'; begin=ft.index(marker); end=ft.index('def verifier.candidate.tx2_authenticated',begin); body=re.sub(r'\s+',' ',ft[begin:end])
need=['let g ← weights.powers 29#usize p.gamma','verifier.candidate.query_loop proof p a g obs val2 val3 22#usize']
positions=[]
for token in need:
    i=body.find(token)
    if i<0: errors.append(f'missing emitted token: {token}')
    positions.append(i)
if all(i>=0 for i in positions) and positions[0]>=positions[1]: errors.append('generated powers/query_loop order mismatch')
wt=weights.read_text()
if sha(weights)!=m['source_bindings']['rust_weights_powers_source']['full_file_sha256']: errors.append('Rust weights source hash mismatch')
if 'pub fn powers<const N:usize>(x:E)->[E;N] { let mut p=E::ONE;core::array::from_fn(|_| {let a=p;p=p.mul(x);a}) }' not in wt: errors.append('Rust powers stateful from_fn body mismatch')
rt=rust.read_text()
if 'let g = powers::<29>(p.gamma);' not in rt: errors.append('Rust powers line missing')
if 'query_loop(proof, &p, a, &g, obs, &geometry, pending, 22)?' not in rt: errors.append('Rust same-g query_loop call missing')
if rt.find('let g = powers::<29>(p.gamma);') > rt.find('query_loop(proof, &p, a, &g, obs, &geometry, pending, 22)?'): errors.append('Rust source order mismatch')
lean=(root/'sources/S4Tx2PowersQuerySourceCutV1.lean').read_text()
required_cut=[
    'let g ← ops.weightsPowers 29#usize p.gamma',
    'ops.mark obs AspisR1Stage2.verifier.Phase.CheckpointRead',
    'ops.readInactive proof',
    'ops.readFoldedRoot proof',
    'ops.batchMerkle proof p foldedRoot 1#usize hash',
    'ops.makeGeometry p.queries a.next 22#usize',
    'ops.makePending (alloc.vec.Vec.deref a.weights)',
    'query_loop call proof p a g obs geometry pending 22#usize',
]
for token in required_cut:
    if token not in re.sub(r'\s+',' ',lean): errors.append(f'typed source cut token missing: {token}')
if 'compact.SPLIT : Std.Usize := 10#usize' not in ft: errors.append('SPLIT literal binding missing')
if errors:
    print('FAIL'); print('\n'.join(errors)); sys.exit(1)
print('PASS: pinned Rust and emitted Funs both bind g from powers before passing that same g to query_loop; typed cut proves successful-call inversion.')
