from pathlib import Path
import json
E=Path(__file__).resolve().parent
native=E/'NIF_native.rs.txt';s=native.read_text()
Q='K{c0:aspis_core::field::CM31{a:M31(r[0]),b:M31(r[1])},c1:aspis_core::field::CM31{a:M31(r[2]),b:M31(r[3])}}'
helper='fn any_raw_q()->K {let r:[u32;4]=kani::any();'+Q+'}'
steps={
'dot_scalar_decode':'let q:[u8;608]=kani::any();let slot:usize=kani::any();let term:usize=kani::any();kani::assume(slot<4 && term<26);let o=slot*120+term*4;let raw:[u8;4]=q[o..o+4].try_into().unwrap();kani::assume(u32::from_le_bytes(raw)<2147483647);let _scalar=M31::from_le_bytes(raw).unwrap();',
'dot_tail0_decode':'let q:[u8;608]=kani::any();let slot:usize=kani::any();kani::assume(slot<4);let o=slot*120+104;for j in 0..4 {let i=o+4*j;kani::assume(u32::from_le_bytes([q[i],q[i+1],q[i+2],q[i+3]])<2147483647);}let _scalar=K::from_le_bytes(&q[o..o+16]).unwrap();',
'dot_tail1_decode':'let q:[u8;608]=kani::any();let slot:usize=kani::any();kani::assume(slot<4);let o=480+slot*32;for j in 0..4 {let i=o+4*j;kani::assume(u32::from_le_bytes([q[i],q[i+1],q[i+2],q[i+3]])<2147483647);}let _scalar=K::from_le_bytes(&q[o..o+16]).unwrap();',
'dot_tail2_decode':'let q:[u8;608]=kani::any();let slot:usize=kani::any();kani::assume(slot<4);let o=480+slot*32+16;for j in 0..4 {let i=o+4*j;kani::assume(u32::from_le_bytes([q[i],q[i+1],q[i+2],q[i+3]])<2147483647);}let _scalar=K::from_le_bytes(&q[o..o+16]).unwrap();',
'dot_coeff_limbs':'let coefficient=any_e();let _limbs=coefficient.to_limbs();',
'dot_reduce_eight':'let limbs:[u64;8]=kani::any();let _value=E::from_limbs([M31::reduce_u64(limbs[0]).0,M31::reduce_u64(limbs[1]).0,M31::reduce_u64(limbs[2]).0,M31::reduce_u64(limbs[3]).0,M31::reduce_u64(limbs[4]).0,M31::reduce_u64(limbs[5]).0,M31::reduce_u64(limbs[6]).0,M31::reduce_u64(limbs[7]).0]).unwrap();',
'dot_tail_new':'let _tail=crate::fast_pairing::EbyKDot::new();',
'dot_final_add':'let value=any_e();let tail=any_e();let _out=value.add(tail);',
'accum_basis_initialize':'let mut basis=[M31::ZERO;256];basis[0]=M31::ONE;let n=1;let _=(basis,n);',
'accum_basis_outer_step':'let mut n:usize=kani::any();let j:usize=kani::any();kani::assume(n>0 && n<64 && j<n);let mut node=M31(kani::any());kani::assume(node.0<2147483647);let mut basis=[M31::ZERO;256];let w:u32=kani::any();kani::assume(w<2147483647);basis[j]=M31(w);basis[n+j]=basis[j].mul(node);node=node.mul(node).double().sub(M31::ONE);n*=2;let _=(basis,node,n);',
'accum_row_accessors':'let row:[u64;4]=kani::any();let limbs:[u32;4]=kani::any();let j:usize=kani::any();kani::assume(j<4);let _old=residue_limb_at(&row,j);let _limb=power_limb_at(&limbs,j);',
'accum_weight_accessor':'let weights=['+','.join(['any_raw_q()']*64)+'];let j:usize=kani::any();kani::assume(j<64);let _out=accumulated_weight_at(&weights,j);',
'accum_basis_accessor':'let r:[u32;256]=kani::any();let basis=['+','.join('M31(r['+str(i)+'])' for i in range(256))+'];let j:usize=kani::any();kani::assume(j<64);let _out=basis_at(&basis,j);',
'accum_trace_weight':'let weight=any_q();let index:usize=kani::any();crate::trace::value(12,index,E::from_qm31(weight));',
'accum_trace_basis':'let raw:u32=kani::any();kani::assume(raw<2147483647);let index:usize=kani::any();crate::trace::value(13,index,E::from_m31(M31(raw)));',
'accum_terms_increment':'let mut terms:usize=kani::any();kani::assume(terms<12);terms+=1;let _=terms;',
'accum_trace_index':'let next:usize=kani::any();let width:usize=kani::any();let j:usize=kani::any();kani::assume(next<22 && width==64 && j<width);let _index=next*width+j;',
'accum_flush_choice':'let terms:usize=kani::any();kani::assume(terms<12);let _flush=terms&3==3;',
'dot_batch_bounds':'let start:usize=kani::any();kani::assume(start<=24 && start%4==0);let _end=core::cmp::min(start+4,26);',
'dot_prefix_borrow':'let bytes:[u8;832]=kani::any();let _q:&[u8;608]=bytes[..608].try_into().unwrap();'
}
assert 'pub fn dot_scalar_decode' not in s
s+='\n'+helper+'\n'+'\n'.join('pub fn '+name+'() {'+body+'}' for name,body in steps.items())+'\n';native.write_text(s)
p=E/'NIF_purity.rs.txt';s=p.read_text();anchor=s.index('fn circle_pure()');start=s.rfind('#[kani::proof]',0,anchor);attrs=s[start:anchor]
for name in steps:
 s+='\n'+attrs+'fn '+name+'_pure() {aspis_r1_cost_probe::verifier::NIF_native::'+name+'();}\n'+attrs+'fn '+name+'_control() {let _=SolanaDigest.digest(&[b"NIF control"]);aspis_r1_cost_probe::verifier::NIF_native::'+name+'();}\n'
p.write_text(s);(E/'NIF_MORE_PLAN.json').write_text(json.dumps(steps,indent=1)+'\n')
print('Prepared 20 independent orchestration windows')
