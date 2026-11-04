use aspis_core::field::{CM31,QM31,M31};
const NFG_P:u32=2147483647;
pub fn NFG_neg_word_ref(x:u32)->u32 {if x==0 {0}else{NFG_P-x}}
pub fn NFG_cm_ref(x:CM31)->CM31 {
 CM31{a:M31(NFG_neg_word_ref(x.a.0)),b:M31(NFG_neg_word_ref(x.b.0))}
}
pub fn NFG_qm_zero_ref(x:QM31)->bool {
 x.c0.a.0==0 && x.c0.b.0==0 && x.c1.a.0==0 && x.c1.b.0==0
}
