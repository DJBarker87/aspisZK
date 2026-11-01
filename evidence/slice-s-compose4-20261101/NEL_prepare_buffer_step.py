"""One pinned copy/fill iteration for a named first-root child window."""
from pathlib import Path
import subprocess,difflib,json,sys,hashlib
E=Path(__file__).resolve().parent;case=sys.argv[1];negative=sys.argv[2]=='negative'
subprocess.run([sys.executable,str(E/'NEL_prepare_window.py'),'1','positive'],check=True)
# All windows are in real descendants of the validator, never another root.
cases={
 'late_fill':('pair_tree_profile.rs',1520,0,1520,'fill',None),
 'late_after_copy':('pair_tree_profile.rs',1520,832,688,'copy','output[32 + POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES..].copy_from_slice(&encoded_afterstate);'),
 'payment_transfer_recipient':('payment_relation.rs',216,152,32,'copy','output[FIRST_OUTPUT_OR_DESTINATION_OFFSET..SECOND_OUTPUT_OFFSET]'),
 'payment_transfer_change':('payment_relation.rs',216,184,32,'copy','output[SECOND_OUTPUT_OFFSET..]'),
 'payment_withdraw_amount':('payment_relation.rs',216,148,4,'copy','output[AMOUNT_OR_RESERVED_OFFSET..FIRST_OUTPUT_OR_DESTINATION_OFFSET]'),
 'payment_withdraw_destination':('payment_relation.rs',216,152,32,'copy','&public.destination_token_account'),
 'payment_withdraw_change':('payment_relation.rs',216,184,32,'copy','&public.change_commitment'),
 'after_root':('pair_terminal.rs',688,16,32,'copy','&afterstate.next_root'),
}
file,N,start,width,kind,needle=cases[case];path='crates/aspis-statement/src/pool_v1/'+file
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
if needle is not None:assert needle in frozen,needle
source='0' if kind=='fill' else 'src[offset]'
expected=f'if j=={start}+offset{{{source}}}else{{old}}'
if negative:expected='('+expected+')^1'
parameters='' if kind=='fill' else f',src:&[u8;{width}]'
args='' if kind=='fill' else ',&src'
setup='' if kind=='fill' else f'let src:[u8;{width}]=kani::any();'
operation='output[offset]=0;' if kind=='fill' else f'let dst=&mut output[{start}..{start+width}];let mut i=offset;dst[i]=src[i];i+=1;'
body=f'''#![allow(non_snake_case)]
#[kani::requires(offset<{width} && j<{N} && old==output[j])]
#[kani::modifies(output)]
#[kani::ensures(|r| *r==offset+1 && output[j]=={expected})]
fn step(output:&mut[u8;{N}],offset:usize,j:usize,old:u8{parameters})->usize{{{operation}offset+1}}
#[kani::proof_for_contract(step)]
fn buffer_step(){{let mut output:[u8;{N}]=kani::any();let offset:usize=kani::any();kani::assume(offset<{width});let j:usize=kani::any();kani::assume(j<{N});let old=output[j];{setup}step(&mut output,offset,j,old{args});}}
'''
changed=frozen+'\n#[cfg(kani)]\n#[path="NEL_buffer_step.rs"]\nmod NEL_buffer_step;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEL_buffer_step.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEL_native_contracts.patch').write_text(patch)
(E/'NEL_BUFFER_CURRENT.json').write_text(json.dumps(dict(case=case,source=path,source_sha256=hashlib.sha256(frozen.encode()).hexdigest(),negative=negative,start=start,width=width,destination_width=N,one_iteration=True,copy_step='exact pinned KMX value operation' if kind=='copy' else 'single scalar assignment of fill iteration; native std fill association remains separate',same_prestate=True,child_reply='arbitrary full fixed array' if kind=='copy' else None,composition='NEJ_WindowStep.iteration and NED_WindowExtensionality; child/source association separate',not_whole_native_root=True),indent=1)+'\n')
