#[derive(Clone,Copy)] pub enum Error { Public }
#[derive(Clone,Copy)] pub struct Public {
 pub withdrawal:bool,pub anchor:[u32;8],pub nullifier:[u32;8],pub asset_id:u32,
 pub recipient:[u32;8],pub change:[u32;8],pub withdrawal_amount:u32,
 pub next_pair_index:u64,pub frontier:[[u32;8];20],pub next_root:[u32;8],pub next_frontier:[[u32;8];20]
}
#[inline(never)] fn canonical(v:u32)->Option<u32>{if v<2147483647 {Some(v)}else{None}}
fn fields(out:&mut [u8;1455],pos:&mut usize,values:&[u32])->Result<(),Error>{
 let mut i=0usize;while i<values.len(){ let v=match canonical(values[i]) {Some(v)=>v,None=>return Err(Error::Public)};
 let mut j=0u32;while j<4 {out[*pos]=(v>>(8u32*j)) as u8;*pos+=1;j+=1;} i+=1;}Ok(())
}
pub fn public_bytes(p:Public)->Result<([u8;1455],usize),Error>{
 let mut out=[0u8;1455];let mut pos=0usize;out[pos]=if p.withdrawal {1}else{0};pos+=1;
 fields(&mut out,&mut pos,&p.anchor)?;fields(&mut out,&mut pos,&p.nullifier)?;
 fields(&mut out,&mut pos,&[p.asset_id])?;out[pos]=if p.withdrawal{0}else{1};pos+=1;
 if !p.withdrawal {fields(&mut out,&mut pos,&p.recipient)?;}
 fields(&mut out,&mut pos,&p.change)?;out[pos]=if p.withdrawal{1}else{0};pos+=1;
 if p.withdrawal {fields(&mut out,&mut pos,&[p.withdrawal_amount])?;}
 let mut j=0u32;while j<8 {out[pos]=(p.next_pair_index>>(8u32*j)) as u8;pos+=1;j+=1;}
 let mut i=0usize;while i<20 {fields(&mut out,&mut pos,&p.frontier[i])?;i+=1;}
 fields(&mut out,&mut pos,&p.next_root)?;
 i=0;while i<20 {fields(&mut out,&mut pos,&p.next_frontier[i])?;i+=1;}
 Ok((out,pos))
}
