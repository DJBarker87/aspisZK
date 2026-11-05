from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
p=E/'NIH_copy.rs.txt';s=p.read_text();assert 'fn NIH_selected_binary' not in s
s+='''
fn NIH_words(q:QM31)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn NIH_q(w:[u32;4])->QM31{QM31{c0:CM31{a:M31(w[0]),b:M31(w[1])},c1:CM31{a:M31(w[2]),b:M31(w[3])}}}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_selected_binary(){
 let raw:[u32;4]=kani::any();let weight:u32=kani::any();let high=NIH_q(raw);
 let out=NIH_words(selected_binary_weight(high,M31(weight)));
 let j:usize=kani::any();kani::assume(j<4);
 assert_eq!(out[j],(if weight==1{raw[j]}else{0}) ^ if cfg!(NIH_invert){1}else{0});
}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_link_weight(){
 let kind:u8=kani::any();let level:u8=kani::any();let append:u64=kani::any();let withdraw:bool=kani::any();
 kani::assume(kind<=4&&level<64);
 let variant=if withdraw{PoolV1PairForestCompiledVariantV1::Withdrawal}else{PoolV1PairForestCompiledVariantV1::PrivateTransfer};
 let endpoint=CompiledPoolV1PairForestEndpoint{row:kani::any(),slot:kani::any(),pattern:kani::any()};
 let link=CompiledPoolV1PairForestLink{tag:kani::any(),weight_kind:kind,weight_level:level,producer:endpoint,consumer:endpoint};
 let out=link_weight(link,append,variant).0;
 let bit=((append>>level)&1) as u32;
 let expected=match kind{0=>1,1=>(!withdraw) as u32,2=>withdraw as u32,3=>1-bit,4=>bit,_=>unreachable!()};
 assert!(out<=1);assert_eq!(out,expected ^ if cfg!(NIH_invert){1}else{0});
}
'''
p.write_text(s)
(E/'NIH_COPY_HELPER_PINS.json').write_text(json.dumps(dict(revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs',harness_sha256=hashlib.sha256(s.encode()).hexdigest(),actual_calls=['selected_binary_weight','link_weight'],domain=['every raw high[4], every u32 weight','kind<=4; level<64; every u64 append index and both variants; other fields arbitrary'],modifies='none; no fields or pointers stubbed'),indent=2)+'\n')
