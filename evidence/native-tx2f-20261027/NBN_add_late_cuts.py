from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-statement/src/pool_v1/pair_tree_profile.rs'],text=True)
a=f.index('    output[..8].copy_from_slice',f.index('pub fn encode_pool_v1_pair_late_public_statement_v1('));b=f.index('    encode_pool_v1_pair_live_snapshot_v1(',a)
body=f[a:b]
s='''
use crate::pool_v1::pair_tree_profile::{POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC,POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION,POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT,POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES,POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES};
fn NBN_late_header(output:&mut[u8;1520]){
'''+body+'''}
#[kani::proof]
#[kani::unwind(1881)]
fn NBN_late_header_gate(){
 let mut out:[u8;1520]=kani::any(); let j:usize=kani::any(); kani::assume(j<1520);
 let old=out[j]; NBN_late_header(&mut out);
 let h:[u8;24]=[65,83,80,76,65,84,69,49,1,2,32,0,32,3,0,0,176,2,0,0,240,5,0,0];
 assert_eq!(out[j],if j<24 {h[j]} else {old});
}
#[kani::proof]
#[kani::unwind(1881)]
fn NBN_fill_iteration(){
 let mut out:[u8;1520]=kani::any();
 let i:usize=kani::any();kani::assume(i<1520);
 let j:usize=kani::any();kani::assume(j<1520);
 let old=out[j];out[i]=0;
 assert_eq!(out[j],if j==i {0} else {old});
}
'''
p=E/'NBN_more.rs.txt';old=p.read_text();assert 'fn NBN_late_header(' not in old;p.write_text(old+s)
(E/'NBN_LATE_CUTS.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs',header_body=body,unwind=1881,scope='one fill iteration and fixed header with full byte frame; no whole fill/codec loop'),indent=2)+'\n')
