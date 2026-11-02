"""Exact late encoder length/index guard, overflow and all u64 inputs."""
from pathlib import Path
import sys,subprocess,difflib,json
E=Path(__file__).resolve().parent;negative=sys.argv[1]=='negative';subprocess.run([sys.executable,str(E/'NEM_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
a=f.index('pub fn encode_pool_v1_pair_late_public_statement_v1(');z=f.index('\n}',a)+2;original=f[a:z]
body='''use super::*;
fn prefix(length:usize,before:u64,after:u64)->Result<(),PoolV1PairLatePublicStatementErrorV1>{if length!=POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES{return Err(PoolV1PairLatePublicStatementErrorV1::WrongLength);}if before.checked_add(ADD)!=Some(after){return Err(PoolV1PairLatePublicStatementErrorV1::AfterstateIndexMismatch);}Ok(())}
#[kani::proof]
fn late_prefix(){let length:usize=kani::any();let before:u64=kani::any();let after:u64=kani::any();let actual=prefix(length,before,after);let expected=if length!=1520{Err(PoolV1PairLatePublicStatementErrorV1::WrongLength)}else if before==u64::MAX||after!=before+1{Err(PoolV1PairLatePublicStatementErrorV1::AfterstateIndexMismatch)}else{Ok(())};assert!(actual==expected,"all length/index values, overflow and rejection prefix before any mutation");}
'''.replace('ADD','2' if negative else '1')
changed=f+'\n#[cfg(kani)]\n#[path="NEM_late_prefix.rs"]\nmod NEM_late_prefix;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p));patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEM_late_prefix.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines());(E/'NEM_native_contracts.patch').write_text(patch)
(E/'NEM_LATE_PREFIX_CURRENT.json').write_text(json.dumps(dict(negative=negative,frozen_body=original,all_usize_lengths=True,all_u64_indices=True,overflow_included=True,exact_prefix=True,no_mutation=True),indent=1)+'\n')
