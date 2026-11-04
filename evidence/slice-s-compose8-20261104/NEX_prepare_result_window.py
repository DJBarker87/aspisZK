"""Result encoder native windows; retain the missing whole-parent association explicitly."""
from NEX_native_patch import E,frozen
import subprocess,sys,json,difflib,hashlib
slot,mode=sys.argv[1:];assert slot in ['header','lane','digest','error'] and mode in ['positive','negative']
subprocess.run([sys.executable,str(E/'NEX_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=frozen(p)
a=f.index('pub fn encode_pool_v1_pair_forest_terminal_result_v1(');z=f.index('\n}',a)+2;whole=f[a:z]
if slot=='header':
 source='output[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC);';width=4;statement='output.copy_from_slice(&POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC);';expected='POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC[j]';args=''
elif slot=='lane':
 source='output[7] = result.output_lane;';width=1;statement='output[0]=lane;';expected='lane';args='let lane:u8=kani::any();'
elif slot=='digest':
 source='output[RESULT_NULLIFIER_OFFSET..RESULT_AFTERSTATE_OFFSET]\n        .copy_from_slice(&encode_digest_canonical(&result.nullifier));';width=32;statement='output.copy_from_slice(&reply);';expected='reply[j]';args='let reply:[u8;32]=kani::any();'
else:
 source='validate_result(result)?;';width=0;statement='';expected='';args=''
assert source in whole
if slot=='error':
 body='''use super::*;
fn continuation(child:Result<(),PoolV1PairForestTerminalFormatErrorV1>)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{child?;Ok(())}
#[kani::proof]
fn result_window(){let child=if kani::any(){Ok(())}else{Err(PoolV1PairForestTerminalFormatErrorV1::WrongLength)};assert!(continuation(child)==child);}
'''
else:
 body=f'''use super::*;
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn result_window(){{let mut output:[u8;{width}]=kani::any();let j:usize=kani::any();kani::assume(j<{width});{args}{statement}assert!(output[j]==({expected}){'^1' if mode=='negative' else ''});}}
'''
h=f+'\n#[cfg(kani)]\n#[path="NEX_result_window.rs"]\nmod NEX_result_window;\n'
patch=''.join(difflib.unified_diff(f.splitlines(True),h.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEX_result_window.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEX_native_contracts.patch').write_text(patch)
(E/'NEX_RESULT_WINDOW_CURRENT.json').write_text(json.dumps(dict(slot=slot,mode=mode,source=body,frozen_statement=source,frozen_body_sha256=hashlib.sha256(whole.encode()).hexdigest(),domain='all local bytes and arbitrary cell in the indicated fixed window; typed child reply for digest',classification='native assignment/copy window projected from frozen encoder; whole792-byte frame, child arguments/results and caller association remain OPEN; error-only two-case cut has NO native composition credit'),indent=1)+'\n')
