from pathlib import Path
import subprocess,sys,json,difflib
E=Path(__file__).resolve().parent;width=int(sys.argv[1]);mode=sys.argv[2];assert width in [4,8,32] and mode in ['positive','negative']
subprocess.run([sys.executable,str(E/'NEQ_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/atomic_statement.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
body='''use super::*;
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn unwrap_payload(){let input:[u8;WIDTH]=kani::any();let j:usize=kani::any();kani::assume(j<WIDTH);let original=input[j];let actual=unwrap_fixed_slice(Ok(input));assert!(actual[j]==originalCORRUPT,"same full fixed-width Ok payload and ownership");}
'''.replace('WIDTH',str(width)).replace('CORRUPT','^1' if mode=='negative' else '')
changed=f+'\n#[cfg(kani)]\n#[path="NEQ_unwrap.rs"]\nmod NEQ_unwrap;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/NEQ_unwrap.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEQ_native_contracts.patch').write_text(patch)
(E/'NEQ_UNWRAP_CURRENT.json').write_text(json.dumps(dict(width=width,mode=mode,domain='actual fixed-width Ok conversions; arbitrary payload and observed index; generic uniform source match',classification='same-byte-array native caller instance for4/8/32 and generic emitted Ok/Err laws; callers must prove successful fixed conversion'),indent=1)+'\n')
