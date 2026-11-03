from pathlib import Path
import subprocess,sys,json,difflib,hashlib
E=Path(__file__).resolve().parent;slot=int(sys.argv[1]);mode=sys.argv[2];assert mode in ['positive','negative','wrong_place']
subprocess.run([sys.executable,str(E/'NEQ_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
a=f.index('pub fn encode_pool_v1_pair_forest_terminal_statement_v1(');z=f.index('\n}',a)+2;fbody=f[a:z]
windows=[(0,4,'POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC'),(4,1,'POOL_V1_PAIR_FOREST_TERMINAL_VERSION'),(5,1,'s.transition_kind() as u8'),(6,1,'POOL_V1_DIGEST_ENCODING_VERSION'),(7,1,'common.output_lane'),(8,32,'common.master_account'),(40,32,'common.checkpoint_account'),(72,32,'common.selected_lane_account'),(104,8,'common.checkpoint_sequence.to_le_bytes()'),(112,32,'reply')]
start,width,expr=windows[slot]
old=(E.parent/'slice-s-compose2-20261029/NEE_K052-NEE_oracle.patch').read_text();a=old.index('+fn NEE_digest()');z=old.index('+#[derive',a);construct='\n'.join(l[1:] for l in old[a:z].splitlines() if l.startswith('+')).replace('super::super::PoolV1PairLiveSnapshotV1','PoolV1PairLiveSnapshotV1')
operation=f'output[{start}]=({expr})'+('^1' if mode=='negative' else '')+';' if width==1 else f'let src=&({expr});let dst=&mut output[{start}..{start+width}];let mut i=offset;dst[i]=src[i]'+('^1' if mode=='negative' else '')+';i+=1;assert!(i==offset+1);'
expected=f'if j=={start}{{{expr}}}else{{old}}' if width==1 else f'if j=={start}+offset{{({expr})[offset]}}else{{old}}'
setup='let reply:[u8;32]=kani::any();'
if slot==9:setup+='let d='+('&common.lane_transition.live_snapshot.current_root' if mode=='wrong_place' else '&common.historical_global_anchor')+';assert!(core::ptr::eq(d,&s.common().historical_global_anchor),"same root digest child argument");'
body='use super::*;\nuse crate::pool_v1::*;\nuse aspis_core::field::M31;\nuse crate::Digest;\n'+construct+'''
#[kani::proof]
fn root_window(){let s=NEE_statement();let common=s.common();let mut output:[u8;1880]=kani::any();let j:usize=kani::any();kani::assume(j<1880);let old=output[j];let offset:usize=kani::any();kani::assume(offset<WIDTH);SETUP OPERATION assert!(output[j]==EXPECTED,"same actual root window and complete frame");}
'''.replace('WIDTH',str(width)).replace('SETUP',setup).replace('OPERATION',operation).replace('EXPECTED',expected)
changed=f+'\n#[cfg(kani)]\n#[path="NEQ_root_window.rs"]\nmod NEQ_root_window;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_root_window.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEQ_native_contracts.patch').write_text(patch)
(E/'NEQ_ROOT_WINDOW_CURRENT.json').write_text(json.dumps(dict(slot=slot,mode=mode,start=start,width=width,expression=expr,frozen_body=fbody,frozen_body_sha256=hashlib.sha256(fbody.encode()).hexdigest(),arbitrary_prestate=True,all_typed_inputs=True,one_KMX_step=width>1,classification='source root field/scalar window; exact digest child input; complete frame; no whole-buffer copy'),indent=1)+'\n')
