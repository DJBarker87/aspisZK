from pathlib import Path
import json
E=Path(__file__).resolve().parent
p=json.loads((E/'NFI_WRAPPER_PAYLOAD.json').read_text());original=json.loads((E/'NFI_ORIGINAL_SPLIT_PAYLOAD.json').read_text())
p['crates/aspis-r1-cost-probe/src/lib.rs']=original['crates/aspis-r1-cost-probe/src/lib.rs']
p['crates/aspis-r1-cost-probe/src/NFI_original.rs']=original['crates/aspis-r1-cost-probe/src/NFI_original.rs']
attr='''#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFI_copy::KMX_copy_nonoverlapping)]
'''
k='crates/aspis-r1-cost-probe/src/NFI_original.rs';s=p[k]
s+=attr+'''fn original_allocation_disjoint_receiver(){
 let proof=[0u8;57607];let receiver:[[u64;4];2]=kani::any();let returned:WideExact=kani::any();
 let base=proof.as_ptr() as usize;let end=base+proof.len();
 let r=&receiver as *const [[u64;4];2] as usize;let out=&returned as *const WideExact as usize;
 assert!(end<=out || out+core::mem::size_of::<WideExact>()<=base);
 let separate=end<=r || r+core::mem::size_of::<[[u64;4];2]>()<=base;
 assert_eq!(separate,if cfg!(NFI_wrong_original_disjoint){false}else{true});
}
'''
p[k]=s;k='crates/aspis-r1-cost-probe/src/NFI_pairing.rs';s=p[k]
for which in ['count','scalar']:
 s+=attr+f'''fn public_{which}_reject_frame(){{
 let old:[[u64;4];2]=kani::any();let count:usize=kani::any();
 kani::assume({'count>=MAX_TERMS' if which=='count' else 'count<MAX_TERMS'});
 let mut receiver=EbyKDot{{c0:Dot{{sums:old[0]}},c1:Dot{{sums:old[1]}},count}};
 let value:E=kani::any();let scalar:QM31=kani::any();
 {'let words=super::super::limbs_of(scalar);kani::assume(words[0]>=P || words[1]>=P || words[2]>=P || words[3]>=P);' if which=='scalar' else ''}
 let mut log=NFI_log();let out=NFI_public_push(&mut receiver,value,scalar,&mut log);
 let half:usize=kani::any();let lane:usize=kani::any();kani::assume(half<2 && lane<4);
 assert!(out.is_err());assert_eq!(log.calls,0);assert_eq!(receiver.count,count);
 let after=if half==0{{receiver.c0.sums[lane]}}else{{receiver.c1.sums[lane]}};
 assert_eq!(after,if cfg!(NFI_wrong_{which}_reject){{old[half][lane]^1}}else{{old[half][lane]}});
}}
'''
sites=json.loads((E/'NFI_RAW_SITES.json').read_text())['sites'];pairs=[('abcd'.index(a),'efgh'.index(b)) for a,b in sites]
for half in range(2):
 s+=attr+f'''fn public_half{half}_raw_arguments(){{
 let value:E=kani::any();let scalar:QM31=kani::any();
 for word in value.to_limbs(){{kani::assume(word<P);}}for word in super::super::limbs_of(scalar){{kani::assume(word<P);}}
 let mut receiver=EbyKDot{{c0:Dot{{sums:kani::any()}},c1:Dot{{sums:kani::any()}},count:0}};
 let mut parent=NFI_log();let accepted=NFI_public_push(&mut receiver,value,scalar,&mut parent);assert!(accepted.is_ok());
 let replies:[u64;16]=kani::any();for i in 0..16{{kani::assume(replies[i]<=4611686009837453316);}}
 let mut raw=NFI_RawLog{{replies,left:[0;16],right:[0;16],order:[99;16],calls:0}};
 let _=NFI_raw(Q(parent.left[{half}]),Q(parent.right[{half}]),&mut raw);
 let at:usize=kani::any();kani::assume(at<16);let pairs={pairs!r};
 assert_eq!(raw.calls,16);assert_eq!(raw.order[at],at);
 assert_eq!(raw.left[at],u64::from(value.to_limbs()[{half*4}+pairs[at].0]));
 let expected=u64::from(super::super::limbs_of(scalar)[pairs[at].1]);
 assert_eq!(raw.right[at],if cfg!(NFI_wrong_half{half}_raw_arguments){{expected^1}}else{{expected}});
}}
'''
s+=attr+'''fn final_carrier_input_frame(){
 let q:[u8;608]=kani::any();let g:[E;29]=kani::any();let old:[[u64;4];2]=kani::any();let head:E=kani::any();
 for word in head.to_limbs(){kani::assume(word<P);}
 let byte:usize=kani::any();let gi:usize=kani::any();let lane:usize=kani::any();kani::assume(byte<608 && gi<29 && lane<8);
 let before=q[byte];let coefficient=g[gi].to_limbs()[lane];
 let tail=EbyKDot{c0:Dot{sums:old[0]},c1:Dot{sums:old[1]},count:3};
 let returned=head.add(tail.finish());
 assert_eq!(q[byte],before);assert_eq!(g[gi].to_limbs()[lane],coefficient);
 let sum=head.to_limbs()[lane]+reduce(if lane<4{old[0][lane]}else{old[1][lane-4]});
 let expected=if sum>=P{sum-P}else{sum};
 assert_eq!(returned.to_limbs()[lane],if cfg!(NFI_wrong_final_input_frame){expected^1}else{expected});
}
'''
p[k]=s;(E/'NFI_CONTEXT_PAYLOAD.json').write_text(json.dumps(p))
s=(E/'NFI_queue2.py').read_text();a=s.index('jobs=');b=s.index('for i,h,wrong in jobs:',a)
s=s[:a]+'''jobs=[(77,'NFI_copy::KMX_checks::KMX_ptr_correct',None),(78,'NFI_copy::KMX_checks::KMX_ptr_wrong',None)]
windows=[('NFI_original::original_allocation_disjoint_receiver','NFI_wrong_original_disjoint')]
windows += [('fast_pairing::canonical::NFI_pairing::'+n,c) for n,c in [('public_count_reject_frame','NFI_wrong_count_reject'),('public_scalar_reject_frame','NFI_wrong_scalar_reject'),('public_half0_raw_arguments','NFI_wrong_half0_raw_arguments'),('public_half1_raw_arguments','NFI_wrong_half1_raw_arguments'),('final_carrier_input_frame','NFI_wrong_final_input_frame')]]
for i,(h,c) in enumerate(windows):
 for j,w in enumerate([None,c]):jobs.append((79+2*i+j,h,w))
'''+s[b:];s=s.replace("'NFI_TAIL_CALL_PAYLOAD.json'","'NFI_CONTEXT_PAYLOAD.json','NFI_KANI_BASE':'NFI_ORIGINAL_BASE.json'");(E/'NFI_queue8.py').write_text(s)
