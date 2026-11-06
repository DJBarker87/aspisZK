from pathlib import Path
import difflib,json,hashlib
E=Path(__file__).resolve().parent
code='''
struct NJL_PathParentLog{calls:usize,selectors:usize,range:[usize;2],left:[[u32;4];4],right:[[u32;4];4],kind:[u8;4],ops:usize,selector:QM31,opened:usize,packed:usize,start:usize,pick:usize,limb:usize,lane:u32}
fn NJL_path_sum(selectors:&Selectors,ranges:&[core::ops::Range<usize>],reply:QM31,l:&mut NJL_PathParentLog)->QM31{assert_eq!(l.calls,0);assert_eq!(ranges.len(),1);l.calls+=1;l.selectors=selectors as*const Selectors as usize;l.range=[ranges[0].start,ranges[0].end];reply}
fn NJL_path_op(left:QM31,right:QM31,kind:u8,reply:QM31,l:&mut NJL_PathParentLog)->QM31{let i=l.ops;assert!(i<4);l.left[i]=NJL_words(left);l.right[i]=NJL_words(right);l.kind[i]=kind;l.ops+=1;reply}
fn NJL_path_reply(selector:QM31,opened:&[QM31;16],reply:[QM31;17],l:&mut NJL_PathParentLog)->[QM31;17]{assert_eq!(l.calls,1);l.calls+=1;l.selector=selector;l.opened=opened as*const[QM31;16]as usize;reply}
fn NJL_path_pack(packed:&mut[QM31;24],start:usize,lanes:&[QM31;17],reply:[QM31;24],l:&mut NJL_PathParentLog){assert_eq!(l.calls,2);l.calls+=1;l.packed=packed as*mut[QM31;24]as usize;l.start=start;l.lane=NJL_words(lanes[l.pick])[l.limb];*packed=reply;}
fn NJL_path_parent(packed:&mut[QM31;24],opened:&[QM31;16],selectors:&Selectors,sum:QM31,ops:[QM31;4],lanes:[QM31;17],reply:[QM31;24],l:&mut NJL_PathParentLog){
 let high=NJL_path_sum(selectors,&[57..63],sum,l);
 let a=NJL_path_op(selectors.low[1],selectors.low[5],1,ops[0],l);
 let b=NJL_path_op(a,selectors.low[9],1,ops[1],l);
 let c=NJL_path_op(b,selectors.low[13],1,ops[2],l);
 let path_selector=NJL_path_op(high,c,0,ops[3],l);
 let path=NJL_path_reply(path_selector,opened,lanes,l);
 NJL_path_pack(packed,32,&path,reply,l);
}
#[kani::proof] #[kani::unwind(67)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJL_path_parent_cut(){
 let selectors=Selectors{high:unsafe{core::mem::transmute::<[[u32;4];64],[QM31;64]>(kani::any())},low:unsafe{core::mem::transmute::<[[u32;4];16],[QM31;16]>(kani::any())}};
 let opened:[QM31;16]=unsafe{core::mem::transmute::<[[u32;4];16],[QM31;16]>(kani::any())};let ops:[QM31;4]=unsafe{core::mem::transmute::<[[u32;4];4],[QM31;4]>(kani::any())};let lanes:[QM31;17]=unsafe{core::mem::transmute::<[[u32;4];17],[QM31;17]>(kani::any())};let reply:[QM31;24]=unsafe{core::mem::transmute::<[[u32;4];24],[QM31;24]>(kani::any())};let mut packed:[QM31;24]=unsafe{core::mem::transmute::<[[u32;4];24],[QM31;24]>(kani::any())};let sum=unsafe{core::mem::transmute::<[u32;4],QM31>(kani::any())};
 let pick:usize=kani::any();let limb:usize=kani::any();let k:usize=kani::any();let op:usize=kani::any();kani::assume(pick<17&&limb<4&&k<24&&op<4);
 let address=&mut packed as*mut[QM31;24]as usize;let mut l=NJL_PathParentLog{calls:0,selectors:0,range:[0;2],left:[[0;4];4],right:[[0;4];4],kind:[0;4],ops:0,selector:QM31::ZERO,opened:0,packed:0,start:0,pick,limb,lane:0};
 NJL_path_parent(&mut packed,&opened,&selectors,sum,ops,lanes,reply,&mut l);
 assert_eq!(l.calls,3);assert_eq!(l.ops,4);assert_eq!(l.range,[57,63]);assert_eq!(l.selectors,&selectors as*const Selectors as usize);
 let left=[selectors.low[1],ops[0],ops[1],sum];let right=[selectors.low[5],selectors.low[9],selectors.low[13],ops[2]];assert_eq!(l.left[op][limb],NJL_words(left[op])[limb]);assert_eq!(l.right[op][limb],NJL_words(right[op])[limb]);assert_eq!(l.kind[op],if op<3{1}else{0});
 assert_eq!(NJL_words(l.selector)[limb],NJL_words(ops[3])[limb]);assert_eq!(l.opened,&opened as*const[QM31;16]as usize);assert_eq!(l.packed,address);assert_eq!(l.start,32);assert_eq!(l.lane,NJL_words(lanes[pick])[limb]);assert_eq!(NJL_words(packed[k])[limb],NJL_words(reply[k])[limb]^if cfg!(NJL_invert){1}else{0});
}
'''
p=E/'NJL_control.rs.txt';old=p.read_text();new=old+code;p.write_text(new);n='crates/aspis-statement/src/pool_v1/NJL_control.rs';(E/'NJL_PATH_PARENT.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)))
pins=json.loads((E/'NJL_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(new.encode()).hexdigest();(E/'NJL_SOURCE_PINS.json').write_text(json.dumps(pins))
p=E/'NJL_gate.py';s=p.read_text();key="frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'";s=s.replace(key,"""p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_path_parent_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_PATH_PARENT.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_PATH_PARENT.patch')],cwd=S,check=True)
"""+key);p.write_text(s)
for k,base in[(39,37),(40,38)]:
 x=json.loads((E/f'NJL_K{base:03}.json').read_text());a=f'NJL_K{k:03}';x.update(attempt=a,module='NJL_path_parent_cut',command=['python3','NJL_gate.py',a+'.json'],expected_time='Optimized path parent LOCAL opaque call log with exact4field operands and full24reply; multiplication Lean-discharged')
 x['native_command']=[v.replace('NJL_occupancy_parent_cut','NJL_path_parent_cut')for v in x['native_command']];x['sources']=list(dict.fromkeys(x['sources']+[p.name for p in E.glob('NJL_*.patch')]));x['collect']=[v.replace(f'NJL_K{base:03}',a)for v in x['collect']];(E/(a+'.json')).write_text(json.dumps(x))
