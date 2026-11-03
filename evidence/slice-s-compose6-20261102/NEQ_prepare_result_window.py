from pathlib import Path
import subprocess,sys,json,difflib,hashlib
E=Path(__file__).resolve().parent;slot=int(sys.argv[1]);mode=sys.argv[2];assert mode in ['positive','negative','wrong_place']
subprocess.run([sys.executable,str(E/'NEQ_prepare_result_validator.py'),'positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
seed=(E/'NEQ_native_contracts.patch').read_text();_,rest=seed.split('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_result_validator.rs\n',1);raw=''.join(l[1:]+'\n' for l in rest.splitlines()[1:] if l.startswith('+'));construct=raw[:raw.index('struct Frame')];a=raw.index('fn result()->');z=raw.index('\n#[kani::proof]',a);construct+=raw[a:z]+'\n'
windows=[(0,4,'POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC'),(4,1,'POOL_V1_PAIR_FOREST_TERMINAL_VERSION'),(5,1,'r.transition_kind as u8'),(6,1,'POOL_V1_DIGEST_ENCODING_VERSION'),(7,1,'r.output_lane'),(8,32,'r.master_account'),(40,32,'r.selected_lane_account'),(72,32,'reply'),(104,688,'reply')]
start,width,expr=windows[slot]
operation=f'output[{start}]=({expr})'+('^1' if mode=='negative' else '')+';' if width==1 else f'let src=&({expr});let dst=&mut output[{start}..{start+width}];let mut i=offset;dst[i]=src[i]'+('^1' if mode=='negative' else '')+';i+=1;assert!(i==offset+1);'
expected=f'if j=={start}{{{expr}}}else{{old}}' if width==1 else f'if j=={start}+offset{{({expr})[offset]}}else{{old}}'
setup=f'let reply:[u8;{width}]=kani::any();'
if slot==7:setup+='let d='+('&r.verified_afterstate.next_root' if mode=='wrong_place' else '&r.nullifier')+';assert!(core::ptr::eq(d,&r.nullifier));'
if slot==8:setup+='let other=NEE_common().lane_transition.candidate_afterstate;let a='+('&other' if mode=='wrong_place' else '&r.verified_afterstate')+';assert!(core::ptr::eq(a,&r.verified_afterstate));'
body=construct+'''
#[kani::proof]
fn result_window(){let r=result();let mut output:[u8;792]=kani::any();let j:usize=kani::any();kani::assume(j<792);let old=output[j];let offset:usize=kani::any();kani::assume(offset<WIDTH);SETUP OPERATION assert!(output[j]==EXPECTED,"same result source field or child reply and complete destination frame");}
'''.replace('WIDTH',str(width)).replace('SETUP',setup).replace('OPERATION',operation).replace('EXPECTED',expected)
changed=f+'\n#[cfg(kani)]\n#[path="NEQ_result_window.rs"]\nmod NEQ_result_window;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_result_window.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEQ_native_contracts.patch').write_text(patch)
a=f.index('pub fn encode_pool_v1_pair_forest_terminal_result_v1(');z=f.index('\n}',a)+2;original=f[a:z]
(E/'NEQ_RESULT_WINDOW_CURRENT.json').write_text(json.dumps(dict(slot=slot,mode=mode,start=start,width=width,expression=expr,frozen_body=original,frozen_body_sha256=hashlib.sha256(original.encode()).hexdigest(),arbitrary_prestate=True,all_typed_inputs=True,one_KMX_step=width>1,classification='result-encoder native scalar/single-copy-step source window; no whole-buffer loop; local support only until selected bridge and full association'),indent=1)+'\n')
