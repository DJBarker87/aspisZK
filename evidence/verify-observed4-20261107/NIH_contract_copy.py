from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
p=E/'NIH_copy_terminal.rs.txt';src=p.read_text();assert 'NIH_selected_ref' not in src
attrs={
'fn selected_binary_weight(high: QM31, weight: M31) -> QM31 {':'''#[cfg_attr(kani,kani::ensures(|result| (*result == NIH_native::NIH_selected_ref(high,weight)) != cfg!(NIH_invert)))]
#[cfg_attr(kani,kani::modifies())]
''',
'fn link_weight(':'''#[cfg_attr(kani,kani::requires(link.weight_kind<=4 && link.weight_level<64))]
#[cfg_attr(kani,kani::ensures(|result| (result.0 == NIH_native::NIH_link_ref(link.weight_kind,link.weight_level,append_index,variant==PoolV1PairForestCompiledVariantV1::Withdrawal)) != cfg!(NIH_invert)))]
#[cfg_attr(kani,kani::modifies())]
'''}
for pat,attr in attrs.items():assert src.count(pat)==1;src=src.replace(pat,attr+pat)
back=src
for attr in attrs.values():back=back.replace(attr,'')
assert back==p.read_text();p.write_text(src)
p=E/'NIH_copy.rs.txt';s=p.read_text();s=s.replace('#[kani::proof]#[kani::unwind(20)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\nfn NIH_selected_binary()', '#[kani::proof_for_contract(super::selected_binary_weight)]#[kani::unwind(20)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\nfn NIH_selected_binary()')
s=s.replace('#[kani::proof]#[kani::unwind(20)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\nfn NIH_link_weight()', '#[kani::proof_for_contract(super::link_weight)]#[kani::unwind(20)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\nfn NIH_link_weight()')
# Controls invert the contract ensures only, while harness assertions keep the SAME intended law.
s=s.replace('(if weight==1{raw[j]}else{0}) ^ if cfg!(NIH_invert){1}else{0}', '(if weight==1{raw[j]}else{0})')
s=s.replace('out,expected ^ if cfg!(NIH_invert){1}else{0}', 'out,expected')
s+='''
pub(super) fn NIH_selected_ref(high:QM31,weight:M31)->QM31{if weight.0==1{high}else{QM31::ZERO}}
pub(super) fn NIH_link_ref(kind:u8,level:u8,index:u64,withdraw:bool)->u32{
 match kind{0=>1,1=>if withdraw{0}else{1},2=>if withdraw{1}else{0},3=>1-((index>>level)&1) as u32,4=>((index>>level)&1) as u32,_=>panic!("invalid link weight")}
}
'''
p.write_text(s)
(E/'NIH_COPY_CONTRACT_ERASURE.json').write_text(json.dumps(dict(attributes=attrs,reverse_erasure=True,source_sha256=hashlib.sha256(src.encode()).hexdigest(),reference_extractions={'selected_binary_ref':'evidence/native-front2-20261028/NDE_E012','link_weight_ref':'evidence/native-front2-20261028/NDE_E004'},modifies='empty; no stub_verified'),indent=2)+'\n')
