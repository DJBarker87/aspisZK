"""Resolve exact request comparison shapes, separate from the 320-byte parent."""
from NEY_native_patch import E,frozen
import sys,json,subprocess,difflib
shape,mode=sys.argv[1:];assert shape in ['magic','zero'] and mode in ['positive','value']
subprocess.run([sys.executable,str(E/'NEY_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=frozen(p);a=f.index('pub fn decode_pool_v1_pair_forest_terminal_request_v1(');z=f.index('\n}',a)+2;original=f[a:z]
if shape=='magic':
 expression='bytes[..4] != POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC';assert expression in original
 code='let bytes:[u8;4]=kani::any();let native=bytes[..4]!=POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC;let model=bytes[0]!=POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC[0]||bytes[1]!=POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC[1]||bytes[2]!=POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC[2]||bytes[3]!=POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC[3];'
else:
 expression='request.verifier_profile == [0u8; 32]';assert expression in original
 code='let bytes:[u8;32]=kani::any();let native=bytes==[0u8;32];let model=bytes[0]==0&&bytes[1]==0&&bytes[2]==0&&bytes[3]==0&&bytes[4]==0&&bytes[5]==0&&bytes[6]==0&&bytes[7]==0&&bytes[8]==0&&bytes[9]==0&&bytes[10]==0&&bytes[11]==0&&bytes[12]==0&&bytes[13]==0&&bytes[14]==0&&bytes[15]==0&&bytes[16]==0&&bytes[17]==0&&bytes[18]==0&&bytes[19]==0&&bytes[20]==0&&bytes[21]==0&&bytes[22]==0&&bytes[23]==0&&bytes[24]==0&&bytes[25]==0&&bytes[26]==0&&bytes[27]==0&&bytes[28]==0&&bytes[29]==0&&bytes[30]==0&&bytes[31]==0;'
body='''use super::*;
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn request_comparison(){'''+code+'assert!(native=='+('!model' if mode=='value' else 'model')+');}\n'
h=f+'\n#[cfg(kani)]\n#[path="NEY_request_comparison.rs"]\nmod NEY_request_comparison;\n'
patch=''.join(difflib.unified_diff(f.splitlines(True),h.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEY_request_comparison.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEY_native_contracts.patch').write_text(patch)
(E/'NEY_REQUEST_COMPARISON_CURRENT.json').write_text(json.dumps(dict(shape=shape,mode=mode,frozen_expression=expression,frozen_body=original,source=body,domain='every typed4-byte header' if shape=='magic' else 'every typed32-byte binding window',classification='exact native slice-versus-array or array-versus-array primitive comparison; parent320-byte record/child/error/frame composition remains OPEN'),indent=1)+'\n')
