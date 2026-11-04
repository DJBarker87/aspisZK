from NFD_native_patch import E,frozen
import sys,subprocess,difflib,json
mode=sys.argv[1];assert mode in ['positive','value']
subprocess.run([sys.executable,str(E/'NFD_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=frozen(p);key='pub fn decode_pool_v1_pair_forest_terminal_request_v1(';a=f.index(key);z=f.index('\n}',a)+2;original=f[a:z]
expr='bytes.len() != POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES';assert expr in original
body='''use super::*;
#[kani::proof]
fn length_gate(){let bytes_len:usize=kani::any();let actual=bytes_len!=POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES;assert!(actual=='''+('!' if mode=='value' else '')+'(bytes_len!=320));}\n'
h=f+'\n#[cfg(kani)]\n#[path="NFD_length.rs"]\nmod NFD_length;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),h.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NFD_length.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NFD_native_contracts.patch').write_text(patch)
(E/'NFD_LENGTH_CURRENT.json').write_text(json.dumps(dict(mode=mode,frozen_body=original,source=body,domain='all usize slice lengths; descriptor projection preserves actual length',classification='exact initial native metadata guard, no byte access on rejected lengths'),indent=1)+'\n')
