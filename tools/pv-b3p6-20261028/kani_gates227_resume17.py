"""Output-component splits and exact caller intervals; all values symbolic.
No renamed rerun: every new gate fixes an actual call interval or selects an
output component. A function receives no full credit from incomplete splits.
"""
from pathlib import Path
import json
P=Path('tools/pv-b3p6-20261028');V=P/'v244';D=Path('evidence/pv-b3p6-20261028/resume17')
lib=(V/'lib_leaf16.rs').read_text()+'\n#[cfg(kani)] mod equivalence17;\n';(V/'lib_leaf17.rs').write_text(lib)
M=P/'v244-leaf17';M.mkdir(exist_ok=True);(M/'Cargo.toml').write_text((P/'v244-leaf16/Cargo.toml').read_text().replace('lib_leaf16.rs','lib_leaf17.rs'))
s='''use aspis_core::field::{QM31,CM31,M31};
use super::equivalence16::{q,qs};
use crate::{host_terminal::remaining16 as d,reference_terminal::remaining16 as r};
use crate::{deployed_poseidon16::access16 as dp,reference_poseidon16::access16 as rp};
fn openings()->aspis_statement::state_only_poseidon::StateOnlyPoseidonOpenings {aspis_statement::state_only_poseidon::StateOnlyPoseidonOpenings{z:qs(),succ_z:qs(),xor12_z:qs()}}
fn lane(n:usize)->usize {let i:usize=kani::any();kani::assume(i<n);i}
fn component(q:QM31,n:usize)->u32 {match n {0=>q.c0.a.0,1=>q.c0.b.0,2=>q.c1.a.0,_=>q.c1.b.0}}
''';gates=[]
def gate(name,function,body,domain='full raw inputs; output index symbolic over its entire type range'):
 global s
 s+='''#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn '''+name+'() {'+body+'}\n'
 gates.append(dict(harness='equivalence17::'+name,function=function,domain=domain,shared_callees=['aspis_core::field::QM31::mul','aspis_core::field::QM31::square'],callee_authority='resume16/SHARED-CALLEES.json',reason='new caller-interval or output-component split; source bodies unchanged; no timeout increase'))
for name,interval in [('zero_57','[0..57]'),('nodes','[4..25,33..57]'),('path','[57..63]')]:
 gate('sum_high_'+name,'sum_high','let h=qs();let l=qs();let ranges='+interval+';assert_eq!(crate::host_terminal::access16::sum(h,l,&ranges),crate::reference_terminal::access16::sum(h,l,&ranges));','full raw arrays; exact interval from deployed host_terminal.rs:250,283,436; these exhaust its three actual call shapes')
for i in range(4):gate('equality_component_'+str(i),'equality_value',f'let a=qs();let b=qs();assert_eq!(component(crate::host_terminal::access16::equality(&a,&b),{i}),component(crate::reference_terminal::access16::equality(&a,&b),{i}));')
for half,proj in [(0,'c0'),(1,'c1')]:
 gate('path_half_'+str(half),'path_lanes_literal',f'let v=q();let o=openings();let k=lane(17);assert_eq!(d::path(v,&o)[k].{proj},r::path(v,&o)[k].{proj});')
 gate('occupancy_half_'+str(half),'occupancy_lanes_literal',f'let a=q();let b=q();let c=M31(kani::any());let v=qs();let k=lane(12);assert_eq!(crate::host_terminal::access16::occupancy(a,b,c,&v)[k].{proj},crate::reference_terminal::access16::occupancy(a,b,c,&v)[k].{proj});')
 gate('internal_pair_half_'+str(half),'interpolated_internal_pair',f'let s=qs();let l=qs();let k=lane(16);assert_eq!(dp::pair(s,&l)[k].{proj},rp::pair(s,&l)[k].{proj});')
 gate('leading_half_'+str(half),'leading_pair_packed',f'let z=qs();let s=qs();let x=qs();let k=lane(4);assert_eq!(dp::leading(z,s,x)[k].{proj},rp::leading(z,s,x)[k].{proj});')
for f,n,c in [('round','full_round','qs()'),('round_m31','full_round_m31_constants','kani::any()'),('round_m31_packed','full_round_m31_constants_packed','kani::any()'),('round_packed','full_round_packed','qs()')]:gate(f+'_index',n,f'let s=qs();let c={c};let k=lane('+('4'if 'packed'in f else '16')+f');assert_eq!(dp::{f}(s,c)[k],rp::{f}(s,c)[k]);')
gate('interpolate_index','interpolate_three_constant_columns','let w=qs();let a=kani::any();let b=kani::any();let c=kani::any();let k=lane(16);assert_eq!(dp::interpolate(w,a,b,c)[k],rp::interpolate(w,a,b,c)[k]);')
gate('poseidon_selectors_index','poseidon_selectors','let h=qs();let l=qs();let k=lane(16);let a=d::poseidon(h,l);let b=r::poseidon(h,l);assert_eq!(a.block,b.block);assert_eq!(a.local[k],b.local[k]);')
for f in ['add_path_lanes','add_value_lanes','add_schedule_lanes']:
 args='&mut a,p,&o,h,l'if f=='add_schedule_lanes' else '&mut a,&o,h,l';args2=args.replace('&mut a','&mut b')
 gate(f+'_index',f,'let mut a=qs();let mut b=a;let o=openings();let h=qs();let l=qs();'+('let p=crate::inputs16::public();'if f=='add_schedule_lanes' else '')+f'd::{f}({args});r::{f}({args2});let k=lane(24);assert_eq!(a[k],b[k]);')
gate('semantic_index','semantic_packed','let p=crate::inputs16::public();let o=openings();let h=qs();let l=qs();let k=lane(24);assert_eq!(d::semantic(p,&o,h,l)[k],r::semantic(p,&o,h,l)[k]);')
gate('initial_index','semantic_initial_and_absorption','let p=crate::inputs16::public();let o=openings();let h=qs();let l=qs();let k=lane(16);let a=d::initial(p,&o,h,l);let b=r::initial(p,&o,h,l);if kani::any(){assert_eq!(a.0[k],b.0[k]);}else{assert_eq!(a.1[k],b.1[k]);}')
gate('digest_index','public_digest_lanes','let p=crate::inputs16::public();let o=openings();let h=qs();let l=qs();let k=lane(8);assert_eq!(d::digests(p,&o,h,l)[k],r::digests(p,&o,h,l)[k]);')
gate('external_index','external_linear_lazy','let s=qs();let k=lane(16);assert_eq!(dp::external(s)[k],rp::external(s)[k]);')
gate('packed_index','external_linear_packed','let s=qs();let k=lane(4);assert_eq!(dp::packed(s)[k],rp::packed(s)[k]);')
gate('projected_index','evaluate_state_only_poseidon_oracle_projected','let z=qs();let s=qs();let x=qs();let b=q();let l=qs();let k=lane(4);assert_eq!(dp::projected(z,s,x,b,l)[k],rp::projected(z,s,x,b,l)[k]);')
assert len(gates)==30,len(gates)
(V/'equivalence17.rs').write_text(s);(D/'KANI-QUEUE.json').write_text(json.dumps([dict(id=73930+i,**g)for i,g in enumerate(gates)],indent=2)+'\n')
