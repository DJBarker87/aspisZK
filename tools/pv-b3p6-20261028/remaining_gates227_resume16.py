"""Function-specific equivalence drafts. Chained arithmetic gates stay unrun
until all required shared-callee binding and domain checks are recorded.
"""
from pathlib import Path
P=Path('tools/pv-b3p6-20261028/v244')
base='''pub(crate) mod remaining16 {use super::*;
fn public(p:crate::inputs16::Public16)->SemanticPublic {SemanticPublic{variant:if p.variant {CompiledVariant::Withdrawal}else{CompiledVariant::PrivateTransfer},pool:p.pool,deployment_domain:p.domain,anchor:p.anchor,nullifier:p.nullifier,asset_id:p.asset,recipient:p.recipient,change:p.change,withdrawal_amount:p.amount,transition:p.transition}}
fn selectors(h:[QM31;64],l:[QM31;16])->Selectors {Selectors{high:h,low:l}}
pub fn validate(p:crate::inputs16::Public16)->Result<(),u8> {validate_transition(public(p)).map_err(|e|e as u8)}
pub fn poseidon(h:[QM31;64],l:[QM31;16])->StateOnlyPoseidonSelectors {poseidon_selectors(&selectors(h,l))}
pub fn path(q:QM31,o:&StateOnlyPoseidonOpenings)->[QM31;17] {path_lanes_literal(q,o)}
pub fn initial(p:crate::inputs16::Public16,o:&StateOnlyPoseidonOpenings,h:[QM31;64],l:[QM31;16])->([QM31;16],[QM31;16]) {semantic_initial_and_absorption(public(p),OPEN,SELECT)}
pub fn digests(p:crate::inputs16::Public16,o:&StateOnlyPoseidonOpenings,h:[QM31;64],l:[QM31;16])->[QM31;8] {public_digest_lanes(public(p),OPEN,SELECT)}
pub fn semantic(p:crate::inputs16::Public16,o:&StateOnlyPoseidonOpenings,h:[QM31;64],l:[QM31;16])->[QM31;24] {semantic_packed(public(p),o,&selectors(h,l))}
pub fn composition(p:crate::inputs16::Public16,c:&[QM31;84],point:&[QM31;10],a:[QM31;3])->Result<(QM31,[QM31;16],[QM31;10],QM31,QM31,QM31),u8> {composition_parts(public(p),c,point,a[0],a[1],a[2]).map_err(|e|e as u8)}
'''
for name in ['add_path_lanes','add_value_lanes','add_schedule_lanes']:
 args='packed,o,&selectors(h,l)' if name!='add_schedule_lanes' else 'packed,public(p),o,&selectors(h,l)'
 p_arg='p:crate::inputs16::Public16,' if name=='add_schedule_lanes' else ''
 base+=f'pub fn {name}(packed:&mut[QM31;24],{p_arg}o:&StateOnlyPoseidonOpenings,h:[QM31;64],l:[QM31;16]) {{{name}({args})}}\n'
base+='}\n'
# Preserve the original exact source prefix and existing adapters.
for side in ['host','reference']:
 p=P/f'{side}_terminal_kani16.rs';s=p.read_text();s=s.split('\npub(crate) mod remaining16')[0]
 w=base.replace('OPEN','o' if side=='host' else '*o').replace('SELECT','&selectors(h,l)' if side=='host' else 'selectors(h,l)')
 p.write_text(s+'\n'+w)
# The following gates cannot be launched unabstracted; source and field domains
# must be separately discharged. They are concrete Rust comparisons, not placeholders.
s='''use super::equivalence16::{q,qs};
use aspis_core::field::{QM31,M31};
use aspis_statement::state_only_poseidon::StateOnlyPoseidonOpenings;
use crate::{host_terminal::remaining16 as d,reference_terminal::remaining16 as r};
fn openings()->StateOnlyPoseidonOpenings {StateOnlyPoseidonOpenings{z:qs(),succ_z:qs(),xor12_z:qs()}}
'''
attrs='''#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
'''
for name,call in [('validate_transition','validate'),('poseidon_selectors','poseidon'),('path_lanes_literal','path'),('semantic_initial_and_absorption','initial'),('public_digest_lanes','digests'),('semantic_packed','semantic'),('composition_parts','composition')]:
 setup='';args=''
 if call=='validate':setup='let p=crate::inputs16::public();';args='p'
 elif call=='poseidon':setup='let h=qs();let l=qs();';args='h,l'
 elif call=='path':setup='let v=q();let o=openings();';args='v,&o'
 elif call=='composition':setup='let p=crate::inputs16::public();let c=qs();let point=qs();let a=qs();';args='p,&c,&point,a'
 else:setup='let p=crate::inputs16::public();let o=openings();let h=qs();let l=qs();';args='p,&o,h,l'
 s+=attrs+f'fn {name}() {{{setup}assert_eq!(d::{call}({args}),r::{call}({args}));}}\n'
for name in ['add_path_lanes','add_value_lanes','add_schedule_lanes']:
 extra='let p=crate::inputs16::public();' if name=='add_schedule_lanes' else '';args='p,&o,h,l' if extra else '&o,h,l'
 s+=attrs+f'fn {name}() {{let mut a=qs();let mut b=a;let o=openings();let h=qs();let l=qs();{extra}d::{name}(&mut a,{args});r::{name}(&mut b,{args});assert_eq!(a,b);}}\n'
for name,call,setup,args in [('absorption_lanes_literal','absorption','let a=qs();let v=qs();','a,&v'),('occupancy_lanes_literal','occupancy','let a=q();let b=q();let c=M31(kani::any());let v=qs();','a,b,c,&v')]:
 s+=attrs+f'fn {name}() {{{setup}assert_eq!(crate::host_terminal::access16::{call}({args}),crate::reference_terminal::access16::{call}({args}));}}\n'
s+=attrs+'fn active_literal() {let h=qs();let l=qs();assert_eq!(crate::host_copy_terminal::access16::active(h,l),crate::reference_copy_terminal::access16::active(h,l));}\n'
s+=attrs+'fn pattern_values_literal() {let v=qs();let l=q();assert_eq!(crate::host_copy_terminal::access16::pattern(&v,l),crate::reference_copy_terminal::access16::pattern(&v,l));}\n'
(P/'remaining_equivalence16.rs').write_text(s)
