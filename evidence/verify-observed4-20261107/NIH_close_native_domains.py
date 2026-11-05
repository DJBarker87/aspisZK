from pathlib import Path
import json
E=Path(__file__).resolve().parent
p=E/'NIH_copy.rs.txt';s=p.read_text();assert 'fn NIH_outer_exhausted'not in s
s+='''
fn NIH_outer_done<const N:usize>(){
 let mut weights:[QM31;N]=core::array::from_fn(|_|NIH_q(kani::any()));let before=weights;
 let coordinates:[QM31;0]=[];let mut iter=coordinates.iter();let len:usize=kani::any();
 let mut log=NIH_OuterLog{coordinate:kani::any(),prepared:PreparedQm31Multiplier::new(QM31::ZERO),prepare_calls:0,inner_calls:0,len:kani::any(),reply:core::array::from_fn(|_|NIH_q(kani::any()))};
 let oldcoord=log.coordinate;let oldlen=log.len;let reply=log.reply;
 let afterlen=NIH_outer_cut(&mut weights,&mut iter,len,&mut log);
 let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<N&&k<4);
 assert_eq!(afterlen,len ^ if cfg!(NIH_invert){1}else{0});assert_eq!(iter.as_slice().len(),0);
 assert_eq!(log.prepare_calls,0);assert_eq!(log.inner_calls,0);assert_eq!(log.len,oldlen);assert_eq!(log.coordinate[k],oldcoord[k]);
 assert_eq!(NIH_words(weights[j])[k],NIH_words(before[j])[k]);assert_eq!(NIH_words(log.reply[j])[k],NIH_words(reply[j])[k]);
}
#[kani::proof]#[kani::unwind(81)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_outer_exhausted(){NIH_outer_done::<16>();NIH_outer_done::<64>();}
''';p.write_text(s)
p=E/'NIH_internal.rs.txt';s=p.read_text();assert 'fn NIH_leading_tail'not in s
s+='''
fn NIH_leading_tail(state:[QM31;16],log:&mut NIH_LeadLog)->[QM31;4]{let middle=NIH_leading_mid(state,log);NIH_leading_last(middle,log)}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_leading_tail_packet(){let before:[QM31;16]=core::array::from_fn(|_|q(kani::any()));let mut log=NIH_lead_log(0);let linear=log.linear_reply;let full=log.full_reply;let reply=log.packed_reply;let out=NIH_leading_tail(before,&mut log);let j:usize=kani::any();let k:usize=kani::any();let r:usize=kani::any();kani::assume(j<16&&k<4&&r<4);assert_eq!(log.calls,3);assert_eq!(words(log.linear_input[j])[k],words(before[j])[k]);assert_eq!(words(log.full_input[j])[k],words(linear[j])[k]);assert_eq!(words(log.packed_input[j])[k],words(full[j])[k]);assert_eq!(log.full_constants[j],EXTERNAL_INITIAL[0][j]);assert_eq!(log.packed_constants[j],EXTERNAL_INITIAL[1][j]);assert_eq!(words(log.linear_reply[j])[k],words(linear[j])[k]);assert_eq!(words(log.full_reply[j])[k],words(full[j])[k]);assert_eq!(words(log.packed_reply[r])[k],words(reply[r])[k]);assert_eq!(words(out[r])[k],words(reply[r])[k] ^ if cfg!(NIH_invert){1}else{0});}
''';p.write_text(s)
(E/'NIH_OUTER_DOMAIN_REPAIR.json').write_text(json.dumps(dict(finding='K047-050 original native outer invariant len<=N/2 is too strong on exhausted actual iterators where len=N; no full row credit from those packets alone',replacement='K095/096 one actual empty-iterator cut for BOTH N16 and N64, ALL usize len, arbitrary full arrays and local log frame. Existing live-iterator native packets are reused without rerun.',reason='source if-let has no len arithmetic on None; exhaustively split live vs exhausted iterator at same emitted stage',unchanged_caps=True,no_success_premise=True),indent=2)+'\n')
x=json.loads((E/'NIH_L066.json').read_text());x.update(module='exhausted expansion domain repair and leading stage inputs',sources=['NIH_install_last.py','NIH_copy.rs.txt','NIH_internal.rs.txt','NIH_OUTER_DOMAIN_REPAIR.json','NIH_LEADING_ERASURE.json'],command=['python3','NIH_install_last.py']);(E/'NIH_L066.json').write_text(json.dumps(x,indent=2)+'\n')
p=E/'NIH_leading_queue.py';s=p.read_text();start=s.index('jobs=');end=s.index('\nfor n,name,negative',start);s=s[:start]+"jobs=[(95,'pool_v1::pair_forest_copy_terminal::NIH_native::NIH_outer_exhausted',False),(96,'pool_v1::pair_forest_copy_terminal::NIH_native::NIH_outer_exhausted',True),(97,'state_only_poseidon::NIH_internal_native::NIH_leading_prefix',False),(98,'state_only_poseidon::NIH_internal_native::NIH_leading_prefix',True),(99,'state_only_poseidon::NIH_internal_native::NIH_leading_tail_packet',False),(100,'state_only_poseidon::NIH_internal_native::NIH_leading_tail_packet',True)]"+s[end:];s=s.replace("'state_only_poseidon::NIH_internal_native::'+name","name");p.write_text(s)
