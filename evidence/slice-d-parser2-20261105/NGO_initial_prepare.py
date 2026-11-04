from pathlib import Path
from NGO_inputs import load,write
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;inputs=load();n='crates/aspis-r1-cost-probe/src/NGO_q.rs'
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/r1_wire.rs'],text=True)
assert 'let mut out = [QM31::ZERO; N];' in frozen
for size in [28,29]:
 inputs[n]+=f'''
#[kani::proof]
#[kani::unwind(33)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NGO_initial_{size}() {{
 let i:usize=kani::any();kani::assume(i<{size});
 let out = [QM31::ZERO; {size}];
 let q=out[i];
 #[cfg(not(NGO_invert))] assert!(q.c0.a.0==0 && q.c0.b.0==0 && q.c1.a.0==0 && q.c1.b.0==0);
 #[cfg(NGO_invert)] assert!(q.c0.a.0==1);
}}
'''
write(inputs)
(E/'NGO_INITIAL_SOURCE.json').write_text(json.dumps(dict(frozen_source_sha256=hashlib.sha256(frozen.encode()).hexdigest(),source_expression='[QM31::ZERO; N]',instantiations=[28,29],property='One arbitrary initialized index; no full-buffer comparison and no caller closure by this fact alone',source_method='Exact native initializer expression, const-generic N instantiated at deployed call sizes'),indent=2))
