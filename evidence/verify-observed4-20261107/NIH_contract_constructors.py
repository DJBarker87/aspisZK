from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent
p=E/'NIH_copy_terminal.rs.txt';s=p.read_text();pat='fn lift_m31(value: M31) -> QM31 {';assert s.count(pat)==1
attr='''#[cfg_attr(kani,kani::ensures(|result| (*result == NIH_native::NIH_lift_ref(value)) != cfg!(NIH_invert)))]
#[cfg_attr(kani,kani::modifies())]
''';s=s.replace(pat,attr+pat);p.write_text(s)
p=E/'NIH_copy.rs.txt';s=p.read_text().replace('#[kani::proof] #[kani::unwind(10)]','#[kani::proof_for_contract(super::lift_m31)] #[kani::unwind(10)]',1);s=s.replace('(if i==0{raw}else{0}) ^ if cfg!(NIH_invert){1}else{0}','(if i==0{raw}else{0})');s+='''
pub(super) fn NIH_lift_ref(value:M31)->QM31{QM31{c0:CM31{a:value,b:M31(0)},c1:CM31{a:M31(0),b:M31(0)}}}
''';p.write_text(s)
p=E/'NIH_raw_extension.rs.txt';s=p.read_text().replace('#[kani::proof] #[kani::unwind(10)]','#[kani::proof_for_contract(super::extension_from_raw_limbs)] #[kani::unwind(10)]',1)
# Keep the original harness's numeric property unchanged; the inverted contract is the control.
s=s.replace(' ^ if cfg!(NIH_invert){1}else{0}','')
s+='''
#[path="NIH_NDE_reference.rs"] mod reference;
pub(super) fn NIH_raw_ref(limbs:[u64;4])->QM31{
 let q=reference::extension_raw_ref(limbs);
 QM31{c0:CM31{a:M31(q.c0.a),b:M31(q.c0.b)},c1:CM31{a:M31(q.c1.a),b:M31(q.c1.b)}}
}
''';p.write_text(s)
(E/'NIH_CONSTRUCTOR_CONTRACTS.json').write_text(json.dumps(dict(lift_attribute=attr,raw_attribute='''#[cfg_attr(kani,kani::requires(limbs[0]<4611686018427387904&&limbs[1]<4611686018427387904&&limbs[2]<4611686018427387904&&limbs[3]<4611686018427387904))]
#[cfg_attr(kani,kani::ensures(|result| (*result == NIH_native::NIH_raw_ref(limbs)) != cfg!(NIH_invert)))]
#[cfg_attr(kani,kani::modifies())]
''',references={'lift':'evidence/native-front2-20261028/NDE_E001','raw':'evidence/native-front2-20261028/NDE_E002'},modifies='empty; no stub_verified'),indent=2)+'\n')
