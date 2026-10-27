from pathlib import Path
import re
R=Path.cwd();D=R/'crates/aspis-r1-cost-probe/src';S=R/'crates/aspis-statement/src/pool_v1'
# Preserve each audit cfg name: forward the selected native features locally.
cargo=R/'crates/aspis-r1-cost-probe/Cargo.toml';s=cargo.read_text();features=re.findall(r'"aspis-statement/(pool-v1-pair-forest-[^"]+)"',s[s.index('optimized-terminal = ['):s.index('\nprover =')]);a=s.index('optimized-terminal = [')+len('optimized-terminal = [');s=s[:a]+''.join('\n    "'+f+'",' for f in features)+s[a:];a=s.index('\nprover =');s=s[:a]+''.join('\n'+f+' = []' for f in features)+s[a:];
if not any('\n'+f+' = []' in cargo.read_text() for f in features):cargo.write_text(s)
# Copy the selected terminal/copy kernels under explicit prover gates. Tests
# remain in the original statement module and are not copied as new modules.
s=(S/'pair_forest_copy_terminal.rs').read_text();s=s[:s.index('\n#[cfg(test)]\nmod tests')]
s=s.replace('use crate::poseidon2::','use aspis_statement::poseidon2::').replace('include!("pair_forest_copy_terminal_constants.rs");','include!("host_copy_terminal_constants.rs");')
s=s.replace('pub(crate) fn boxed_at_point(point: &[QM31; 10]) -> Box<Self> {\n        Box::new(Self::at_point(point))\n    }','pub(crate) fn boxed_at_point(point: &[QM31;10])->Self {Self::at_point(point)}')
s=s.replace('use alloc::{boxed::Box, vec};','use alloc::vec;')
(D/'host_copy_terminal.rs').write_text(s);(D/'host_copy_terminal_constants.rs').write_bytes((S/'pair_forest_copy_terminal_constants.rs').read_bytes())
s=(S/'pair_forest_semantic_terminal.rs').read_text();a=s.index('\n#[cfg(test)]\nmod tests');b=s.index('/// R0\'s width-29 view',a);s=s[:a]+'\n'+s[b:];a=s.rfind('\n#[cfg(',s.index('pub mod r0'),s.index('mod public_serializer_tests'));s=s[:a]
s=s.replace('use crate::{','use aspis_statement::{',1).replace('use super::{','use aspis_statement::pool_v1::{',1)
s=s.replace('    pair_forest_copy_terminal::{\n        evaluate_with_selectors, PoolV1PairForestCompiledVariantV1, Selectors,\n    },\n','')
s=s.replace('pub const POOL_V1_PAIR_FOREST_TERMINAL_ROWS_V1', 'use crate::host_copy_terminal::{evaluate_with_selectors,PoolV1PairForestCompiledVariantV1,Selectors};\n\npub const POOL_V1_PAIR_FOREST_TERMINAL_ROWS_V1',1)
s=s.replace('include!("pair_forest_semantic_terminal_constants.rs");','include!("host_terminal_constants.rs");')
s=s.replace('#[cfg(feature = "r0")]\npub mod r0', '#[cfg(feature = "prover")]\npub mod r0')
s=s.replace('let selected = core::array::from_fn(|i| claims[i / 28][i % 28]);','let mut selected=[QM31::ZERO;84];let mut i=0usize;while i<84 {selected[i]=claims[i/28][i%28];i+=1;}')
# Keep all terminal rejection branches; remove only the combinator closure.
a=s.index('            terminal_parts(',s.index('pub fn terminal_qm31('));b=s.index('\n        }',a)
part=s[a:b];part=part.replace('            terminal_parts(', '            match terminal_parts(').replace('            )\n            .map(|parts| parts.0)\n            .map_err(|_| Error::Public)', '            ) {Ok(parts)=>Ok(parts.0),Err(_)=>Err(Error::Public)}');s=s[:a]+part+s[b:]
(D/'host_terminal.rs').write_text(s);(D/'host_terminal_constants.rs').write_bytes((S/'pair_forest_semantic_terminal_constants.rs').read_bytes())
s=(R/'evidence/pv-route2-20261027/dropfree/probes/226.rs').read_text();s=s[s.index('#[derive(Clone,Copy)] pub struct Public'):];s=s.replace('pub struct Public','pub struct OwnedPublic').replace('p:Public','p:OwnedPublic').replace('pub fn public_bytes(', 'pub fn encode_owned(')
head='''//! Prover-local public byte carrier and selected terminal wrapper.
use alloc::vec::Vec;
use aspis_core::{field::{M31,QM31},state_only_prefix::r0::{Error,Challenges}};
use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
'''
s=head+s
s+='''
pub fn project(public:Public<'_>)->OwnedPublic {
 let (withdrawal,anchor,nullifier,asset_id,recipient,change,withdrawal_amount,transition)=match public{
  Public::Transfer(p,t)=>(false,p.anchor_root,p.nullifier,p.asset_id,p.recipient_commitment,p.change_commitment,0,t),
  Public::Withdrawal(p,t)=>(true,p.anchor_root,p.nullifier,p.asset_id,[M31::ZERO;8],p.change_commitment,p.amount,t)
 };
 let mut out=OwnedPublic{withdrawal,anchor:[0;8],nullifier:[0;8],asset_id:asset_id.0,recipient:[0;8],change:[0;8],withdrawal_amount,next_pair_index:transition.live_snapshot.next_pair_index,frontier:[[0;8];20],next_root:[0;8],next_frontier:[[0;8];20]};
 let mut i=0usize;while i<8 {out.anchor[i]=anchor[i].0;out.nullifier[i]=nullifier[i].0;out.recipient[i]=recipient[i].0;out.change[i]=change[i].0;out.next_root[i]=transition.candidate_afterstate.next_root[i].0;i+=1;}
 let mut level=0usize;while level<20{let mut i=0usize;while i<8{out.frontier[level][i]=transition.live_snapshot.frontier[level][i].0;out.next_frontier[level][i]=transition.candidate_afterstate.next_frontier[level][i].0;i+=1;}level+=1;}
 out
}
pub fn public_bytes(public:Public<'_>)->Result<([u8;1455],usize),Error>{encode_owned(project(public))}
pub fn materialize_public_bytes(public:Public<'_>)->Result<Vec<u8>,Error>{let (bytes,len)=public_bytes(public)?;Ok(bytes[..len].to_vec())}
pub fn terminal_qm31(public:Public<'_>,claims:&[[QM31;29];3],alpha:&[QM31;10],c:&Challenges)->Result<QM31,Error>{
 let p=match public{Public::Transfer(p,t)=>crate::host_terminal::r0::Public::Transfer(p,t),Public::Withdrawal(p,t)=>crate::host_terminal::r0::Public::Withdrawal(p,t)};
 p.terminal_qm31(claims,alpha,c)
}
'''
(D/'host_public.rs').write_text(s)
p=D/'lib.rs';p.write_text(p.read_text()+''.join('\n#[cfg(feature="prover")]\npub mod '+m+';\n' for m in ['host_copy_terminal','host_terminal','host_public']))
for f in ['host_semantic.rs','prover.rs','sim.rs']:
 p=D/f;s=p.read_text();s=s.replace('public.public_bytes()', 'crate::host_public::materialize_public_bytes(public)')
 s=s.replace('self.public.terminal_qm31(&claims,point,self.challenges)', 'crate::host_public::terminal_qm31(self.public,&claims,point,self.challenges)')
 s=s.replace('public.terminal_qm31(&zero,p,&ch)', 'crate::host_public::terminal_qm31(public,&zero,p,&ch)').replace('public.terminal_qm31(&claims,&alpha,&ch)', 'crate::host_public::terminal_qm31(public,&claims,&alpha,&ch)')
 p.write_text(s)
