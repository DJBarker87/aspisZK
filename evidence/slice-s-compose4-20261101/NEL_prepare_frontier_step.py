from pathlib import Path
import sys,subprocess,difflib,json,hashlib
E=Path(__file__).resolve().parent;case,mode=sys.argv[1:];negative=mode=='negative';assert case in ['live','after']
subprocess.run([sys.executable,str(E/'NEL_prepare_window.py'),'1','positive'],check=True)
file='pair_tree_profile.rs' if case=='live' else 'pair_terminal.rs';path='crates/aspis-statement/src/pool_v1/'+file
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
base=160 if case=='live' else 48;N=800 if case=='live' else 688
assert ('let start = '+str(base)+' + 32 * level;') in frozen
body=f'''use super::*;
struct Frame{{expected:*const Digest,reply:[u8;32],called:bool}}
fn encode(d:&Digest,f:&mut Frame)->[u8;32]{{assert!(!f.called && (d as *const Digest)==f.expected,"same frontier digest place");f.called=true;f.reply}}
#[kani::requires(level<20 && offset<32 && j<{N} && old==out[j] && !f.called && f.expected==(&nodes[level] as *const Digest))]
#[kani::modifies(out,&mut f.called)]
#[kani::ensures(|r| *r==offset+1 && f.called && out[j]==if j=={base}+32*level+offset{{f.reply[offset]}}else{{old}})]
fn step(nodes:&[Digest;20],out:&mut[u8;{N}],level:usize,offset:usize,j:usize,old:u8,f:&mut Frame)->usize{{
 let mut iter=nodes[level..].iter();let node=iter.next().unwrap();assert!(core::ptr::eq(node,&nodes[level]));assert!(iter.as_slice().len()==19-level && iter.as_slice().as_ptr()==nodes[level+1..].as_ptr());assert!(level+1<=20);
 let reply=encode(ARG,f);let start={base}+32*level;let dst=&mut out[start..start+32];let src=&reply;let mut i=offset;dst[i]=src[i];i+=1;i
}}
fn digest()->Digest{{[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}}
#[kani::proof_for_contract(step)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn frontier_step(){{let nodes=[{','.join(['digest()']*20)}];let mut out:[u8;{N}]=kani::any();let level:usize=kani::any();kani::assume(level<20);let offset:usize=kani::any();kani::assume(offset<32);let j:usize=kani::any();kani::assume(j<{N});let old=out[j];let mut f=Frame{{expected:&nodes[level] as *const Digest,reply:kani::any(),called:false}};step(&nodes,&mut out,level,offset,j,old,&mut f);}}
'''.replace('ARG','&nodes[(level+1)%20]' if negative else 'node')
changed=frozen+'\n#[cfg(kani)]\n#[path="NEL_frontier_step.rs"]\nmod NEL_frontier_step;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEL_frontier_step.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEL_native_contracts.patch').write_text(patch)
(E/'NEL_FRONTIER_CURRENT.json').write_text(json.dumps(dict(case=case,negative=negative,source=path,source_sha256=hashlib.sha256(frozen.encode()).hexdigest(),base=base,destination_width=N,frontier_width=20,one_native_iterator_step=True,one_KMX_copy_step=True,arbitrary_full_prestate=True,exact_child_place=True,full_arbitrary_digest_reply=True,no_new_copy_stub=True,classification='rule B native iteration; source/emitted cursor and sequential frame association remain separate'),indent=1)+'\n')
