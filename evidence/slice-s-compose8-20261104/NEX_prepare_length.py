"""Effect-free slice metadata gate, before the frozen first payload access."""
from NEX_native_patch import E,frozen
import subprocess,sys,json,difflib,hashlib
mode=sys.argv[1];assert mode in ['positive','negative']
subprocess.run([sys.executable,str(E/'NEX_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=frozen(p);a=f.index('pub fn decode_pool_v1_pair_forest_terminal_statement_v1(');z=f.index('    if bytes[..4]',a);prefix=f[a:z]
body='''use super::*;
fn length_gate(length:usize)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{if length!=POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES{return Err(PoolV1PairForestTerminalFormatErrorV1::WrongLength);}Ok(())}
#[kani::proof]
fn length_gate_all(){let length:usize=kani::any();assert!(length_gate(length)==if length==@WIDTH@{Ok(())}else{Err(PoolV1PairForestTerminalFormatErrorV1::WrongLength)});}
'''.replace('@WIDTH@','1881' if mode=='negative' else '1880')
h=f+'\n#[cfg(kani)]\n#[path="NEX_length.rs"]\nmod NEX_length;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),h.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEX_length.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEX_native_contracts.patch').write_text(patch)
(E/'NEX_LENGTH_CURRENT.json').write_text(json.dumps(dict(mode=mode,frozen_prefix=prefix,source=body,domain='all usize metadata lengths; immutable typed Slice.len identity is the existing primitive ABI/std interpretation',classification='slice metadata projection before any payload access; full scalar guard plus frozen prefix/no-read check, kernel wrong_length and fixed_carrier partition; not a whole buffer proof',trust='P6/D188 option A reclassification; no new trust item'),indent=1))
