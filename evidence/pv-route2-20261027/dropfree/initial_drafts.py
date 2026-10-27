# Historical initial drafts; final probes and source-manifest.json are authoritative.
from pathlib import Path
import re,json
D=Path(__file__).resolve().parent; R=Path.cwd(); P=D/'probes'
def save(op,s): (P/f'{op}.rs').write_text(s)
# Samplers: eliminate from_le_bytes dependency closure and all panic formatting.
s=(R/'evidence/pv-route2-20261027/probes/249.rs').read_text()
s=re.sub(r'u32::from_le_bytes\(\[block\[4\*i\],block\[4\*i\+1\],block\[4\*i\+2\],block\[4\*i\+3\]\]\)', '(block[4*i] as u32) | ((block[4*i+1] as u32)<<8u32) | ((block[4*i+2] as u32)<<16u32) | ((block[4*i+3] as u32)<<24u32)',s)
s=s.replace('<< 32','<< 32u32')
# debug_assert are erased by optimized release profile; preserve them in source.
save(249,s);save(250,s)
w=(R/'crates/aspis-r1-cost-probe/src/weights.rs').read_text(); pts=(R/'crates/aspis-core/src/state_only_prefix.rs').read_text();pts=pts[pts.index('fn state_only_statement_points('):pts.index('\nfn encode_statement_points(')]
pts=pts.replace('for coordinate in (0..z.len()).rev() {','let mut coordinate=10usize; while coordinate>0 { coordinate-=1;')
body=w[w.index('        let points=',w.index('pub fn new(')):w.index('\n    pub fn raw(')]
body=body[:body.rfind('\n    }')];body=body.replace('aspis_core::state_only_prefix::r0::statement_points','state_only_statement_points').replace('Ok(Self::box_from_parts(variant, factors, points, extra))','Ok(Weights {variant,factors,points,extra})')
body=body.replace('for k in 0..3 { for d in 0..5 {','let mut k=0usize; while k<3 { let mut d=0usize; while d<5 {').replace('        }}','        d+=1;} k+=1;}').replace('for k in 0..2 {','let mut k=0usize; while k<2 {').replace('for d in 1..5 {','let mut d=1usize; while d<5 {').replace('x=double(y);','x=double(y);d+=1;').replace('        }\n        Ok','        k+=1;}\n        Ok')
save(252,'''use aspis_core::field::QM31;
use aspis_core::field::QM31 as K;
use aspis_core::circle::SecureCirclePoint;
#[derive(Clone,Copy)] pub enum Variant { S1,S2,D }
#[derive(Clone,Copy)] pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation }
const TAU:[usize;5]=[3,4,2,0,1];
#[derive(Clone,Copy)] pub struct Weights {pub variant:Variant,pub factors:[[[K;4];5];5],pub points:[[K;10];3],pub extra:[K;2]}
fn double(x:K)->K { x.mul(x).add(x.mul(x)).sub(K::ONE) }
'''+pts+'\npub fn weights_new(variant:Variant,alpha:&[K;10],z:&[SecureCirclePoint;2])->Result<Weights,Error> {\n'+body+'\n}\n')
# Public bytes copies the exact semantic projection into a Drop-free carrier.
save(226,'''#[derive(Clone,Copy)] pub enum Error { Public }
#[derive(Clone,Copy)] pub struct Public {
 pub withdrawal:bool,pub anchor:[u32;8],pub nullifier:[u32;8],pub asset_id:u32,
 pub recipient:Option<[u32;8]>,pub change:[u32;8],pub withdrawal_amount:Option<u32>,
 pub next_pair_index:u64,pub frontier:[[u32;8];20],pub next_root:[u32;8],pub next_frontier:[[u32;8];20]
}
fn fields(out:&mut [u8;1423],pos:&mut usize,values:&[u32])->Result<(),Error>{
 let mut i=0usize;while i<values.len(){ let v=values[i]; if v>=2147483647 {return Err(Error::Public);}
 let mut j=0u32;while j<4 {out[*pos]=(v>>(8u32*j)) as u8;*pos+=1;j+=1;} i+=1;}Ok(())
}
pub fn public_bytes(p:Public)->Result<([u8;1423],usize),Error>{
 let mut out=[0u8;1423];let mut pos=0usize;out[pos]=if p.withdrawal {1}else{0};pos+=1;
 fields(&mut out,&mut pos,&p.anchor)?;fields(&mut out,&mut pos,&p.nullifier)?;
 fields(&mut out,&mut pos,&[p.asset_id])?;out[pos]=if p.recipient.is_some(){1}else{0};pos+=1;
 if let Some(value)=p.recipient {fields(&mut out,&mut pos,&value)?;}
 fields(&mut out,&mut pos,&p.change)?;out[pos]=if p.withdrawal_amount.is_some(){1}else{0};pos+=1;
 if let Some(value)=p.withdrawal_amount {fields(&mut out,&mut pos,&[value])?;}
 let mut j=0u32;while j<8 {out[pos]=(p.next_pair_index>>(8u32*j)) as u8;pos+=1;j+=1;}
 let mut i=0usize;while i<20 {fields(&mut out,&mut pos,&p.frontier[i])?;i+=1;}
 fields(&mut out,&mut pos,&p.next_root)?;
 i=0;while i<20 {fields(&mut out,&mut pos,&p.next_frontier[i])?;i+=1;}
 Ok((out,pos))
}
''')
# Exact endpoint-only schedule from the shipped legacy constructor, with path replacement.
links=[(f*16+11,t*16) for f,t in [(1,2),(2,3),(25,26),(27,28),(28,29),(30,31),(31,32)]]
links += [(11,28),(12,412),(44,428),(60,428)]
# Legacy private path links are filtered out, as in forest constructor.
links += [(44,960),(460,962),(508,964),(960,966),(962,966),(964,967),(966,967),(64,969),(865,969),(523,970),(475,540),(523,540),(970,528)]
links += [( (33+l)*16+11,(34+l)*16+12) for l in []] # appended interleaved below
for l in range(20):links += [((33+l)*16+11,(34+l)*16+12),((33+l)*16+11,(34+l)*16)]
assert len(links)==64
links=[(a+48 if a>=864 else a,b+48 if b>=864 else b) for a,b in links]
for l in range(24):
 aux=912+(l//4)*16+[1,5,9,13][l%4];target=4+l if l<=20 else 33+l;prev=3 if l==0 else (3+l if l<=21 else 32+l)
 links += [(prev*16+11,aux),(aux+1,target*16+12),(aux+1,target*16)]
assert len(links)==136
save(134,'''#[derive(Clone,Copy)] pub enum Error {Shape,EndpointCapacity{row:u16}}
const LINKS:[(u16,u16);136]=['''+','.join(f'({a},{b})' for a,b in links)+'''];
pub fn active_row_masks()->Result<[u16;64],Error>{
 let mut producers=[0u8;1024];let mut consumers=[0u8;1024];let mut masks=[0u16;64];
 let mut i=0usize;while i<136 {let (a,b)=LINKS[i];let p=a as usize;let c=b as usize;
 if p>=1024 || producers[p]>=2 {return Err(Error::EndpointCapacity{row:a});}producers[p]+=1;
 if c>=1024 || consumers[c]>=2 {return Err(Error::EndpointCapacity{row:b});}consumers[c]+=1;
 masks[p>>4u32]|=1u16<<((p&15) as u32);masks[c>>4u32]|=1u16<<((c&15) as u32);i+=1;}
 Ok(masks)
}
''')
