from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=json.loads((E/'NFI_TAIL_FRAME_PAYLOAD.json').read_text());k='crates/aspis-r1-cost-probe/src/NFI_pairing.rs';s=p[k]
attr='''#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFI_copy::KMX_copy_nonoverlapping)]
'''
for call in range(3):
 coeff=[28,26,27][call];offset='slot*120+104' if call==0 else f'480+slot*32+{call-1}*16'
 s+=attr+f'''fn tail_parser_push{call}_frame(){{
 let q:[u8;608]=kani::any();let g:[E;29]=kani::any();let slot:usize=kani::any();
 let lane:usize=kani::any();let half:usize=kani::any();let observed:usize=kani::any();
 kani::assume(slot<4 && lane<4 && half<2 && observed<608);
 let offset={offset};
 for i in 0..4{{let at=offset+4*i;kani::assume(u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]])<P);}}
 let old:[[u64;4];2]=kani::any();let mut receiver=EbyKDot{{c0:Dot{{sums:old[0]}},c1:Dot{{sums:old[1]}},count:{call}}};
 let pointer=[&mut receiver.c0 as *mut Dot as usize,&mut receiver.c1 as *mut Dot as usize];
 let qp=q.as_ptr() as usize;let gp=g.as_ptr() as usize;let byte=q[observed];let coefficient=g[{coeff}].to_limbs()[half*4+lane];
 let scalar=QM31::from_le_bytes(&q[offset..offset+16]).unwrap();
 let mut log=NFI_log();let returned=NFI_public_push(&mut receiver,g[{coeff}],scalar,&mut log);
 assert!(returned.is_ok());assert_eq!(receiver.count,{call+1});assert_eq!(log.calls,2);
 assert_eq!(log.receiver[half],pointer[half]);assert_eq!(log.before[half][lane],old[half][lane]);
 assert_eq!(log.right[half][lane],u32::from_le_bytes([q[offset+lane*4],q[offset+lane*4+1],q[offset+lane*4+2],q[offset+lane*4+3]]));
 assert_eq!(q.as_ptr() as usize,qp);assert_eq!(g.as_ptr() as usize,gp);assert_eq!(q[observed],byte);
 assert_eq!(g[{coeff}].to_limbs()[half*4+lane],coefficient);
 assert_eq!(log.left[half][lane],if cfg!(NFI_wrong_tail_call{call}){{coefficient^1}}else{{coefficient}});
 let actual=if half==0{{receiver.c0.sums[lane]}}else{{receiver.c1.sums[lane]}};
 assert_eq!(actual,log.replies[half][lane]);
}}
'''
p[k]=s;(E/'NFI_TAIL_CALL_PAYLOAD.json').write_text(json.dumps(p))
