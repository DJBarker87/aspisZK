from NMD_formal import *
import subprocess
subprocess.run([sys.executable,str(E/'NMD_shape_queue.py'),'72','marker'],check=True)
from NMD_actual import native
path='crates/aspis-r1-cost-probe/src/verifier.rs'
attrs=['#[cfg_attr(kani,kani::requires(obs.is_none() && p==Phase::Parsed))]\n','#[cfg_attr(kani,kani::modifies())]\n','#[cfg_attr(kani,kani::ensures(|out| *out==()))]\n']
write=lambda xs:(E/'NMD_EXTRA_CONTRACTS.json').write_text(json.dumps({path:{'fn mark(obs:Observer,p:Phase)':xs}},indent=1)+'\n')
write(attrs)
for i,n in enumerate(['NMD_actual_marker_contract','NMD_actual_marker_caller','NMD_actual_marker_caller_inverse','NMD_actual_marker_stability'],78):native(f'NMD_K{i:03}','verifier::candidate::NMD_native::'+n)
write([s.replace('*out==()','*out!=()') for s in attrs]);native('NMD_K082','verifier::candidate::NMD_native::NMD_actual_marker_contract');write(attrs)
