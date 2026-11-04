"""Actual frozen exact::<8/32>, full bounded slice Result with KMX."""
import sys,subprocess,json,difflib
from NEX_native_patch import E,frozen
width=int(sys.argv[1]);mode=sys.argv[2];assert width in [8,32] and mode in ['positive','negative']
subprocess.run([sys.executable,str(E/'NEX_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_terminal.rs';f=frozen(p)
body=f'''use super::*;
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn exact_cut(){{let bytes:[u8;33]=kani::any();let len:usize=kani::any();let j:usize=kani::any();kani::assume(len<=33&&j<{width});let result=exact::<{width}>(&bytes[..len]);if len=={width}{{let out=result.unwrap();assert!(out[j]==bytes[j]{'^1' if mode=='negative' else ''});}}else{{assert!(matches!(result,Err(PoolV1PairVerifierTransportErrorV1::WrongLength)));}}}}
'''
h=f+'\n#[cfg(kani)]\nmod NEX_exact;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),h.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEX_exact.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEX_native_contracts.patch').write_text(patch)
(E/'NEX_EXACT_CURRENT.json').write_text(json.dumps(dict(width=width,mode=mode,domain='width in {8,32}; live slice length <=33; all bytes unrestricted',source=body,frozen_body=f[f.index('fn exact<'):f.index('\n}',f.index('fn exact<'))+2]),indent=1))
