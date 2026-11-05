from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs'
src=subprocess.check_output(['git','show',rev+':'+path],text=True)
start=src.index('        for coordinate in coordinates {');end=src.index('\n        weights\n',start);original=src[start:end]
innerstart=original.index('            for index in (0..len).rev() {');innerend=original.index('\n            len *= 2;',innerstart);inner=original[innerstart:innerend]
body=original.replace('for coordinate in coordinates {','if let Some(coordinate)=iter.next() {').replace('PreparedQm31Multiplier::new(*coordinate)','NIH_prepare(*coordinate,log)').replace(inner,'            NIH_inner(weights,&prepared,len,log);')
assert body.replace('if let Some(coordinate)=iter.next() {','for coordinate in coordinates {').replace('NIH_prepare(*coordinate,log)','PreparedQm31Multiplier::new(*coordinate)').replace('            NIH_inner(weights,&prepared,len,log);',inner)==original
out='''
struct NIH_OuterLog<const N:usize>{coordinate:[u32;4],prepared:PreparedQm31Multiplier,prepare_calls:usize,inner_calls:usize,len:usize,reply:[QM31;N]}
fn NIH_prepare<const N:usize>(coordinate:QM31,log:&mut NIH_OuterLog<N>)->PreparedQm31Multiplier{
 log.coordinate=NIH_words(coordinate);log.prepare_calls+=1;PreparedQm31Multiplier::new(coordinate)
}
fn NIH_inner<const N:usize>(weights:&mut[QM31;N],prepared:&PreparedQm31Multiplier,len:usize,log:&mut NIH_OuterLog<N>){
 log.prepared=*prepared;log.inner_calls+=1;log.len=len;*weights=log.reply;
}
fn NIH_outer_cut<const N:usize>(weights:&mut[QM31;N],iter:&mut core::slice::Iter<QM31>,mut len:usize,log:&mut NIH_OuterLog<N>)->usize{
'''+body+'''
 len
}
fn NIH_outer_window<const N:usize,const C:usize>(){
 let coordinates:[QM31;C]=core::array::from_fn(|_|{let q=NIH_q(kani::any());kani::assume(NIH_canon(q));q});
 let mut weights:[QM31;N]=core::array::from_fn(|_|NIH_q(kani::any()));let before=weights;
 let reply:[QM31;N]=core::array::from_fn(|_|NIH_q(kani::any()));
 let pos:usize=kani::any();kani::assume(pos<=C);let mut iter=coordinates[pos..].iter();
 let len:usize=kani::any();kani::assume(len>0&&len<=N/2);
 let mut log=NIH_OuterLog{coordinate:kani::any(),prepared:PreparedQm31Multiplier::new(QM31::ZERO),prepare_calls:0,inner_calls:0,len:kani::any(),reply};
 let afterlen=NIH_outer_cut(&mut weights,&mut iter,len,&mut log);
 let j:usize=kani::any();let limb:usize=kani::any();kani::assume(j<N&&limb<4);
 assert_eq!(afterlen,if pos<C{2*len}else{len});assert_eq!(iter.as_slice().len(),if pos<C{C-pos-1}else{0});
 assert_eq!(log.prepare_calls,if pos<C{1}else{0});assert_eq!(log.inner_calls,if pos<C{1}else{0});
 if pos<C{assert_eq!(log.coordinate[limb],NIH_words(coordinates[pos])[limb]);assert_eq!(log.len,len);}
 assert_eq!(NIH_words(weights[j])[limb],NIH_words(if pos<C{reply[j]}else{before[j]})[limb] ^ if cfg!(NIH_invert){1}else{0});
 assert_eq!(NIH_words(log.reply[j])[limb],NIH_words(reply[j])[limb]);
}
#[kani::proof]#[kani::unwind(81)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_outer16(){NIH_outer_window::<16,4>();}
#[kani::proof]#[kani::unwind(81)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_outer64(){NIH_outer_window::<64,6>();}
'''
p=E/'NIH_copy.rs.txt';assert 'fn NIH_outer_window'not in p.read_text();p.write_text(p.read_text()+out)
(E/'NIH_OUTER_ERASURE.json').write_text(json.dumps(dict(revision=rev,path=path,original=original,inner_loop=inner,cut=body,reverse_erasure=True,domain='N16/C4 or N64/C6; arbitrary iterator suffix; 0<len<=N/2; coordinate canonical; weights/reply arbitrary raw words',modifies='local weights overwritten by logged inner reply only; local iterator consumes one coordinate; returned len; local log; coordinates immutable',inner_packet='NHU K057/058,N64 K070-075; NHU_ExpandFrame; JFy_SelectorInner.source/FJa_SplitFold.value',prepare_packet='FIv_PreparedNewTotal.value; actual unchanged Prepared::new runs natively'),indent=2)+'\n')
