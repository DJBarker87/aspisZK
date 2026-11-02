"""One step of frozen late-encoder header writes; all remaining fields separate."""
from pathlib import Path
import subprocess,difflib,json,sys
E=Path(__file__).resolve().parent;case=int(sys.argv[1]);negative=sys.argv[2]=='negative';assert 5<=case<7
# Reuse only the empty oracle-file container; the actual module is reversible.
subprocess.run([sys.executable,str(E/'NEL_prepare_window.py'),'1','positive'],check=True)
path='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs';frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
starts=[0,8,9,10,12,16,20];sizes=[8,1,1,2,4,4,4]
values=['POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC','[POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION]','[POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT]','(POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES as u16).to_le_bytes()','(POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES as u32).to_le_bytes()','(POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES as u32).to_le_bytes()','(POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES as u32).to_le_bytes()']
start,size=starts[case],sizes[case];value=values[case]
expected=f'if j=={start}+offset{{({value})[offset]}}else{{old}}'
if negative:expected='('+expected+')^1'
body='''#![allow(non_snake_case)]
use super::*;
#[kani::requires(offset<SIZE && j<POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES && old==output[j])]
#[kani::modifies(output)]
#[kani::ensures(|r| *r==offset+1 && output[j]==@EXPECTED@)]
fn step(output:&mut [u8;POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES],offset:usize,j:usize,old:u8)->usize{
 let dst=&mut output[START..END];let src=&(@VALUE@);let mut i=offset;
 dst[i]=src[i];i+=1;i
}
#[kani::proof_for_contract(step)]
fn header_window(){let mut output:[u8;POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES]=kani::any();let j:usize=kani::any();kani::assume(j<POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES);let old=output[j];let offset:usize=kani::any();kani::assume(offset<SIZE);step(&mut output,offset,j,old);}
'''.replace('SIZE',str(size)).replace('START',str(start)).replace('END',str(start+size)).replace('@VALUE@',value).replace('@EXPECTED@',expected)
changed=frozen+'\n#[cfg(kani)]\n#[path="NEL_late_step.rs"]\nmod NEL_late_step;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEL_late_step.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEL_native_contracts.patch').write_text(patch)
(E/'NEL_WINDOW_CURRENT.json').write_text(json.dumps(dict(case=case,start=start,size=size,value=value,negative=negative,one_iteration=True,source=path,scope='late child header, a real dependency of validator root; no other slice root started',other_header_and_child_frames='OPEN'),indent=1)+'\n')
