from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=json.loads((E/'NFI_FRAME_PAYLOAD.json').read_text());key='crates/aspis-r1-cost-probe/src/NFI_pairing.rs';s=p[key]
attr='''#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFI_copy::KMX_copy_nonoverlapping)]
'''
s+=attr+'''fn tail_initializer_frame(){
 let mut tail=EbyKDot::new();let k:usize=kani::any();kani::assume(k<4);
 assert_eq!(tail.count,0);assert_eq!(tail.c0.sums[k],0);
 assert_ne!(&mut tail.c0 as *mut Dot as usize,&mut tail.c1 as *mut Dot as usize);
 assert_eq!(tail.c1.sums[k],if cfg!(NFI_wrong_tail_init){1}else{0});
}
'''
for half in range(2):
 s+=attr+f'''fn raw_to_half{half}_frame(){{
 let left:[u32;4]=kani::any();let right:[u32;4]=kani::any();
 for i in 0..4{{kani::assume(left[i]<P && right[i]<P);}}
 let replies:[u64;16]=kani::any();for i in 0..16{{kani::assume(replies[i]<=4611686009837453316);}}
 let mut log=NFI_RawLog{{replies,left:[0;16],right:[0;16],order:[99;16],calls:0}};
 let old:[[u64;4];2]=kani::any();let count:usize=kani::any();
 let mut receiver=EbyKDot{{c0:Dot{{sums:old[0]}},c1:Dot{{sums:old[1]}},count}};
 let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<4 && k<4);
 let raw=NFI_raw(Q(left),Q(right),&mut log);let raw_before=raw[k];
 let receiver_place=&mut receiver.c{half} as *mut Dot as usize;
 NFI_dot_step(&mut receiver.c{half},&raw,j);
 assert_eq!(&mut receiver.c{half} as *mut Dot as usize,receiver_place);
 assert_eq!(receiver.c{1-half}.sums[k],old[{1-half}][k]);assert_eq!(receiver.count,count);
 assert_eq!(raw[k],raw_before);assert_eq!(log.calls,16);
 let expected=if j==k{{old[{half}][k].wrapping_add((raw[k]&u64::from(P)).wrapping_add(raw[k]>>31))}}else{{old[{half}][k]}};
 assert_eq!(receiver.c{half}.sums[k],if cfg!(NFI_wrong_raw_half{half}){{expected^1}}else{{expected}});
}}
'''
s+=attr+'''fn private_cursor_to_step_frame(){
 let old:[u64;4]=kani::any();let raw:[u64;4]=kani::any();
 let cursor:usize=kani::any();let k:usize=kani::any();kani::assume(cursor<4 && k<4);
 let mut dot=Dot{sums:old};let mut iter=cursor..4;let j=iter.next().unwrap();
 let same_raw=raw[k];let place=&mut dot as *mut Dot as usize;
 NFI_dot_step(&mut dot,&raw,j);
 assert_eq!(raw[k],same_raw);assert_eq!(&mut dot as *mut Dot as usize,place);
 assert_eq!(iter.start,cursor+1);assert_eq!(iter.end,4);
 let expected=if k==cursor{old[k].wrapping_add((raw[k]&u64::from(P)).wrapping_add(raw[k]>>31))}else{old[k]};
 assert_eq!(dot.sums[k],if cfg!(NFI_wrong_private_cursor){expected^1}else{expected});
}
'''
s+=attr+'''fn private_exhaust_to_caller_frame(){
 let old:[[u64;4];2]=kani::any();let count:usize=kani::any();
 let receiver=EbyKDot{c0:Dot{sums:old[0]},c1:Dot{sums:old[1]},count};
 let mut iter=4..4;assert_eq!(iter.next(),None);
 let k:usize=kani::any();kani::assume(k<4);
 assert_eq!(receiver.c0.sums[k],old[0][k]);assert_eq!(receiver.c1.sums[k],old[1][k]);
 assert_eq!(receiver.count,if cfg!(NFI_wrong_private_exhaust){count^1}else{count});
}
'''
s+=attr+'''fn halves_to_count_frame(){
 let old:[[u64;4];2]=kani::any();let count:usize=kani::any();kani::assume(count<MAX_TERMS);
 let mut receiver=EbyKDot{c0:Dot{sums:old[0]},c1:Dot{sums:old[1]},count};
 receiver.count+=1;let returned:Result<(),()>=Ok(());
 let k:usize=kani::any();kani::assume(k<4);
 assert!(returned.is_ok());assert_eq!(receiver.c0.sums[k],old[0][k]);assert_eq!(receiver.c1.sums[k],old[1][k]);
 assert_eq!(receiver.count,if cfg!(NFI_wrong_count_frame){count+2}else{count+1});
}
'''
s+=attr+'''fn finish_to_final_carrier_frame(){
 let old:[[u64;4];2]=kani::any();let count:usize=kani::any();let head:E=kani::any();
 for word in head.to_limbs(){kani::assume(word<P);}
 let receiver=EbyKDot{c0:Dot{sums:old[0]},c1:Dot{sums:old[1]},count};
 let finished=receiver.finish();let returned=head.add(finished);
 let lane:usize=kani::any();kani::assume(lane<8);
 let selected=if lane<4{old[0][lane]}else{old[1][lane-4]};
 assert_eq!(finished.to_limbs()[lane],reduce(selected));
 let sum=head.to_limbs()[lane]+reduce(selected);let expected=if sum>=P{sum-P}else{sum};
 assert_eq!(returned.to_limbs()[lane],if cfg!(NFI_wrong_final_carrier){expected^1}else{expected});
}
'''
p[key]=s;(E/'NFI_TAIL_FRAME_PAYLOAD.json').write_text(json.dumps(p));(E/'NFI_pairing.rs.txt').write_text(s)
