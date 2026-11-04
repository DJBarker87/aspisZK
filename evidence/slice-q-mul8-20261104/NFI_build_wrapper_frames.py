from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=json.loads((E/'NFI_DISJOINT_PAYLOAD.json').read_text());key='crates/aspis-r1-cost-probe/src/NFI_dots.rs';s=p[key]
attr='''#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFI_copy::KMX_copy_nonoverlapping)]
'''
for slot in range(4):
 s+=attr+f'''fn wrapper_slot{slot}_installation(){{
 let q:[u8;609]=kani::any();let g:[WideExact;29]=kani::any();let replies:[WideExact;4]=kani::any();
 let byte:usize=kani::any();let gi:usize=kani::any();let lane:usize=kani::any();
 kani::assume(byte<609 && gi<29 && lane<8);
 let original=q[byte];let coefficient=g[gi].to_limbs()[lane];
 let mut log=NFI_ChildLog{{calls:0,slots:[99;4],qptr:[0;4],gptr:[0;4],replies}};
 let out=NFI_four(&q,&g,&mut log);
 assert_eq!(log.calls,4);assert_eq!(log.slots[{slot}],{slot});
 assert_eq!(log.qptr[{slot}],q.as_ptr() as usize);assert_eq!(log.gptr[{slot}],g.as_ptr() as usize);
 assert_eq!(q[byte],original);assert_eq!(g[gi].to_limbs()[lane],coefficient);
 let expected=replies[{slot}].to_limbs()[lane];
 assert_eq!(out[{slot}].to_limbs()[lane],if cfg!(NFI_wrong_wrapper_slot{slot}){{expected^1}}else{{expected}});
}}
'''
s+=attr+'''fn wrapper_prefix_failure(){
 let q:[u8;608]=kani::any();let len:usize=kani::any();kani::assume(len<608);
 let prefix=q[..len].get(..608);
 assert_eq!(prefix.is_none(),if cfg!(NFI_wrong_wrapper_prefix){false}else{true});
}
'''
p[key]=s;(E/'NFI_WRAPPER_PAYLOAD.json').write_text(json.dumps(p))
s=(E/'NFI_queue2.py').read_text();a=s.index('jobs=');b=s.index('for i,h,wrong in jobs:',a)
s=s[:a]+'''jobs=[(65,'NFI_copy::KMX_checks::KMX_ptr_correct',None),(66,'NFI_copy::KMX_checks::KMX_ptr_wrong',None)]
windows=[(f'wrapper_slot{i}_installation',f'NFI_wrong_wrapper_slot{i}') for i in range(4)]+[('wrapper_prefix_failure','NFI_wrong_wrapper_prefix')]
for i,(h,c) in enumerate(windows):
 for j,w in enumerate([None,c]):jobs.append((67+2*i+j,'fast_dots::NFI_dots::'+h,w))
'''+s[b:];s=s.replace("'NFI_TAIL_CALL_PAYLOAD.json'","'NFI_WRAPPER_PAYLOAD.json'");(E/'NFI_queue7.py').write_text(s)
