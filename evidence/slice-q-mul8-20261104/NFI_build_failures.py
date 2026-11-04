from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=json.loads((E/'NFI_TAIL_CALL_PAYLOAD.json').read_text());base=json.loads((E/'NFI_BASE.json').read_text())
lib='crates/aspis-r1-cost-probe/src/lib.rs';p[lib]+='\n#[cfg(kani)] mod NFI_failures;\n';base[lib]=p[lib]
attr='''#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFI_copy::KMX_copy_nonoverlapping)]
'''
s='''use aspis_core::field::{M31,QM31,WideExact};
const P:u32=2147483647;
struct NFI_Cut{calls:usize,aborted:bool,scalar:u32}
fn NFI_main_parser(q:&[u8;608],slot:usize,term:usize,cut:&mut NFI_Cut)->Option<M31>{
 let parsed=M31::from_le_bytes(q[slot*120+term*4..slot*120+term*4+4].try_into().unwrap());
 match parsed{None=>{cut.aborted=true;None},Some(s)=>{cut.scalar=s.0;cut.calls+=1;Some(s)}}
}
'''
s+=attr+'''fn main_failure_prefix(){
 let q:[u8;608]=kani::any();let slot:usize=kani::any();let term:usize=kani::any();
 let observed:usize=kani::any();kani::assume(slot<4 && term<26 && observed<608);
 let at=slot*120+term*4;let word=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 let byte=q[observed];let mut cut=NFI_Cut{calls:0,aborted:false,scalar:0};
 let returned=NFI_main_parser(&q,slot,term,&mut cut);
 assert_eq!(q[observed],byte);
 if word>=P{assert!(returned.is_none());assert!(cut.aborted);assert_eq!(cut.calls,0);}else{
 assert_eq!(returned.unwrap().0,word);assert!(!cut.aborted);assert_eq!(cut.calls,1);assert_eq!(cut.scalar,word);}
 assert_eq!(cut.aborted,if cfg!(NFI_wrong_main_failure){word<P}else{word>=P});
}
'''
s+=attr+'''fn tail_failure_prefix(){
 let q:[u8;16]=kani::any();let index:usize=kani::any();kani::assume(index<4);
 let words=[u32::from_le_bytes([q[0],q[1],q[2],q[3]]),u32::from_le_bytes([q[4],q[5],q[6],q[7]]),u32::from_le_bytes([q[8],q[9],q[10],q[11]]),u32::from_le_bytes([q[12],q[13],q[14],q[15]])];
 let valid=words[0]<P && words[1]<P && words[2]<P && words[3]<P;
 let before=q[index];let returned=QM31::from_le_bytes(&q);
 assert_eq!(q[index],before);
 if valid{let v=returned.unwrap();let out=[v.c0.a.0,v.c0.b.0,v.c1.a.0,v.c1.b.0];assert_eq!(out[index],words[index]);}
 assert_eq!(returned.is_none(),if cfg!(NFI_wrong_tail_failure){valid}else{!valid});
}
'''
f=json.loads((E.parent/'slice-q-mul7-20261104/NFF_FROZEN.json').read_text())['crates/aspis-r1-cost-probe/src/fast_dots.rs'];a=f.index('        let mut value =');b=f.index('        let mut tail=',a)
s+='fn NFI_head(limbs:[u64;8])->WideExact{\n'+f[a:b].replace('let mut value =','let value =')+'value\n}\n'
s+=attr+'''fn head_to_tail_frame(){
 let limbs:[u64;8]=kani::any();let lane:usize=kani::any();kani::assume(lane<8);
 let head=NFI_head(limbs);let expected=M31::reduce_u64(limbs[lane]).0;
 let tail=crate::fast_pairing::EbyKDot::new();let finished=tail.finish();
 assert_eq!(finished.to_limbs()[lane],0);assert!(head.to_limbs()[lane]<P);
 assert_eq!(head.to_limbs()[lane],if cfg!(NFI_wrong_head_tail){expected^1}else{expected});
}
'''
s+=attr+'''fn main_parser_state_frame(){
 let q:[u8;608]=kani::any();let slot:usize=kani::any();let term:usize=kani::any();
 let lane:usize=kani::any();kani::assume(slot<4 && term<26 && lane<8);
 let limbs:[u64;8]=kani::any();let before=limbs[lane];let mut cut=NFI_Cut{calls:0,aborted:false,scalar:0};
 let at=slot*120+term*4;let word=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 let _=NFI_main_parser(&q,slot,term,&mut cut);
 assert_eq!(cut.calls,if word<P{1}else{0});
 assert_eq!(limbs[lane],if cfg!(NFI_wrong_main_state){before^1}else{before});
}
'''
s+=attr+'''fn tail_parser_state_frame(){
 let q:[u8;16]=kani::any();let g:[WideExact;29]=kani::any();let term:usize=kani::any();let lane:usize=kani::any();
 kani::assume(term<29 && lane<8);let original=g[term].to_limbs()[lane];let receiver:[u64;8]=kani::any();let before=receiver[lane];
 let _=QM31::from_le_bytes(&q);
 assert_eq!(receiver[lane],before);
 assert_eq!(g[term].to_limbs()[lane],if cfg!(NFI_wrong_tail_state){original^1}else{original});
}
'''
p['crates/aspis-r1-cost-probe/src/NFI_failures.rs']=s
(E/'NFI_FAILURE_PAYLOAD.json').write_text(json.dumps(p));(E/'NFI_FAILURE_BASE.json').write_text(json.dumps(base));(E/'NFI_failures.rs.txt').write_text(s)
