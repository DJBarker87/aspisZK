from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs';src=subprocess.check_output(['git','show',rev+':'+path],text=True)
start=src.index('    pub(crate) fn at_point(');end=src.index('\n    #[inline(never)]',start);original=src[start:end]
cut=original.replace('pub(crate) fn at_point(point: &[QM31; 10]) -> Self','fn NIH_atpoint_cut(point: &[QM31; 10],log:&mut NIH_AtLog) -> Selectors').replace('        Self {','        Selectors {').replace('Self::expand(&point[..6])','NIH_expand_high(&point[..6],log)').replace('Self::expand(&point[6..])','NIH_expand_low(&point[6..],log)')
assert cut.replace('fn NIH_atpoint_cut(point: &[QM31; 10],log:&mut NIH_AtLog) -> Selectors','pub(crate) fn at_point(point: &[QM31; 10]) -> Self').replace('        Selectors {','        Self {').replace('NIH_expand_high(&point[..6],log)','Self::expand(&point[..6])').replace('NIH_expand_low(&point[6..],log)','Self::expand(&point[6..])')==original
out='''
struct NIH_AtLog{high_point:[[u32;4];6],low_point:[[u32;4];4],high:[QM31;64],low:[QM31;16],calls:usize}
fn NIH_expand_high(point:&[QM31],log:&mut NIH_AtLog)->[QM31;64]{assert_eq!(log.calls,0);assert_eq!(point.len(),6);log.high_point=core::array::from_fn(|i|NIH_words(point[i]));log.calls+=1;log.high}
fn NIH_expand_low(point:&[QM31],log:&mut NIH_AtLog)->[QM31;16]{assert_eq!(log.calls,1);assert_eq!(point.len(),4);log.low_point=core::array::from_fn(|i|NIH_words(point[i]));log.calls+=1;log.low}
'''+cut+'''
fn NIH_atpoint_window(boxed:bool){
 let point:[QM31;10]=core::array::from_fn(|_|{let q=NIH_q(kani::any());kani::assume(NIH_canon(q));q});
 let high:[QM31;64]=core::array::from_fn(|_|NIH_q(kani::any()));let low:[QM31;16]=core::array::from_fn(|_|NIH_q(kani::any()));
 let mut log=NIH_AtLog{high_point:kani::any(),low_point:kani::any(),high,low,calls:0};
 let out=if boxed{*Box::new(NIH_atpoint_cut(&point,&mut log))}else{NIH_atpoint_cut(&point,&mut log)};
 let h:usize=kani::any();let l:usize=kani::any();let k:usize=kani::any();let i:usize=kani::any();kani::assume(h<64&&l<16&&k<4&&i<6);
 assert_eq!(log.calls,2);assert_eq!(log.high_point[i][k],NIH_words(point[i])[k]);if i<4{assert_eq!(log.low_point[i][k],NIH_words(point[6+i])[k]);}
 assert_eq!(NIH_words(out.high[h])[k],NIH_words(high[h])[k] ^ if cfg!(NIH_invert){1}else{0});assert_eq!(NIH_words(out.low[l])[k],NIH_words(low[l])[k]);
 assert_eq!(NIH_words(log.high[h])[k],NIH_words(high[h])[k]);assert_eq!(NIH_words(log.low[l])[k],NIH_words(low[l])[k]);
}
#[kani::proof]#[kani::unwind(81)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_atpoint(){NIH_atpoint_window(false);}
#[kani::proof]#[kani::unwind(81)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_boxed_atpoint(){NIH_atpoint_window(true);}
'''
p=E/'NIH_copy.rs.txt';assert 'fn NIH_atpoint_window'not in p.read_text();p.write_text(p.read_text()+out)
(E/'NIH_ATPOINT_ERASURE.json').write_text(json.dumps(dict(revision=rev,path=path,original=original,cut=cut,reverse_erasure=True,boxed_original='Box::new(Self::at_point(point))',boxed_cut='Box::new(NIH_atpoint_cut(&point,&mut log))',domains='canonical point[10]; prefix6 to expand64; suffix4 to expand16; arbitrary logged raw return arrays instantiated by NIH_ExpandOuter/NHU_ExpandPacket',modifies='local log/call count; output record; boxed case retained Std Box allocation with abort-prefix semantics under an; point immutable'),indent=2)+'\n')
