from pathlib import Path
import subprocess,json,difflib,hashlib
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';root='crates/aspis-statement/src/pool_v1/'
def frozen(name):return subprocess.check_output(['git','show',REV+':'+root+name],text=True)
s=frozen('pair_terminal.rs');a=s.index('    let mut output = [0u8;',s.index('pub fn encode_pool_v1_pair_verified_afterstate_v1'));b=s.index('    for (level,',a)
action=s[a:b].replace('&encode_digest_canonical(&afterstate.next_root)','&root').replace('afterstate.next_pair_index','index')
code='''use super::*;
use crate::pool_v1::pair_tree_profile::*;
fn NBK_after_prefix(index:u64,root:[u8;32])->[u8;688]{
'''+action+'''output}
#[kani::proof]
fn NBK_after_prefix_gate(){
 let index:u64=kani::any();let root:[u8;32]=kani::any();let j:usize=kani::any();kani::assume(j<688);
 let out=NBK_after_prefix(index,root);
 let expected=if j<4{b"ASJA"[j]}else if j<8{1}else if j<16{index.to_le_bytes()[j-8]}else if j<48{root[j-16]}else{0};
 assert_eq!(out[j],expected);
}
'''
s=frozen('pair_tree_profile.rs');a=s.index('    output.fill(0);',s.index('pub fn encode_pool_v1_pair_live_snapshot_v1'));b=s.index('    for (level,',a)
action2=s[a:b].replace('&encode_digest_canonical(&snapshot.current_root)','&root')
for old,new in [('snapshot.pool','pool'),('snapshot.deployment_domain','domain'),('snapshot.sequence','sequence'),('snapshot.next_pair_index','index')]:action2=action2.replace(old,new)
code+='''fn NBK_live_prefix(output:&mut[u8;800],pool:[u8;32],domain:[u8;32],sequence:u64,index:u64,root:[u8;32]){
'''+action2+'''}
#[kani::proof]
fn NBK_live_prefix_gate(){
 let mut output:[u8;800]=kani::any();let pool:[u8;32]=kani::any();let domain:[u8;32]=kani::any();let sequence:u64=kani::any();let index:u64=kani::any();let root:[u8;32]=kani::any();let j:usize=kani::any();kani::assume(j<800);
 NBK_live_prefix(&mut output,pool,domain,sequence,index,root);
 let expected=if j<8{POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC[j]}else if j==8{1}else if j<16{0}else if j<48{POOL_V1_PAIR_TREE_FORMAT_BINDING[j-16]}else if j<80{pool[j-48]}else if j<112{domain[j-80]}else if j<120{sequence.to_le_bytes()[j-112]}else if j<128{index.to_le_bytes()[j-120]}else if j<160{root[j-128]}else{0};
 assert_eq!(output[j],expected);
}
'''
p=E/'NBK_more.rs.txt';old=p.read_text();i=old.index('#[kani::proof]\nfn NBK_master_sequence_step_gate');p.write_text(old[:i]+code)
jobs=json.loads((E/'NBK_MORE_JOBS.json').read_text());jobs[-2:]=[['NBK_K059','NBK_after_prefix_gate'],['NBK_K060','NBK_live_prefix_gate']];(E/'NBK_MORE_JOBS.json').write_text(json.dumps(jobs,indent=2)+'\n')
x=json.loads((E/'NBK_MORE_PROVENANCE.json').read_text());x['native_header_cuts']={'afterstate':action,'live':action2,'lower_dependency':'NBK_Dep_DigestEncode for the SAME root bytes, open; no stubbed successful digest call'};(E/'NBK_MORE_PROVENANCE.json').write_text(json.dumps(x,indent=2)+'\n')
p=root+'pair_terminal.rs';old=frozen('pair_terminal.rs');new=old+'\n#[cfg(kani)]\n#[path="NBK_codecs.rs"]\nmod NBK_codecs;\n\n#[cfg(kani)]\n#[path="NBK_more.rs"]\nmod NBK_more;\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
for name in ['NBK_codecs','NBK_more']:
 s=(E/(name+'.rs.txt')).read_text();p=root+name+'.rs';patch+=''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/'+p))
(E/'NBK_harness_next.patch').write_text(patch)
