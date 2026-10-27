#[derive(Clone,Copy)] pub enum Error { Public }
#[derive(Clone,Copy)] pub struct Public {
 pub withdrawal:bool,pub anchor:[u32;8],pub nullifier:[u32;8],pub asset_id:u32,
 pub recipient:[u32;8],pub change:[u32;8],pub withdrawal_amount:u32,
 pub next_pair_index:u64,pub frontier:[[u32;8];20],pub next_root:[u32;8],pub next_frontier:[[u32;8];20]
}
#[inline(never)] fn canonical(v:u32)->Option<u32>{if v<2147483647 {Some(v)}else{None}}
fn fields(out:&mut [u8;1455],pos:&mut usize,values:&[u32])->Result<(),Error>{
 let mut i=0usize;while i<values.len(){ let v=match canonical(values[i]) {Some(v)=>v,None=>return Err(Error::Public)};
 out[*pos]=(v>>0u32) as u8;*pos+=1;out[*pos]=(v>>8u32) as u8;*pos+=1;out[*pos]=(v>>16u32) as u8;*pos+=1;out[*pos]=(v>>24u32) as u8;*pos+=1; i+=1;}Ok(())
}
pub fn public_bytes(p:Public)->Result<([u8;1455],usize),Error>{
 let mut out=[0u8;1455];let mut pos=0usize;out[pos]=if p.withdrawal {1}else{0};pos+=1;
 fields(&mut out,&mut pos,&p.anchor)?;fields(&mut out,&mut pos,&p.nullifier)?;
 fields(&mut out,&mut pos,&[p.asset_id])?;out[pos]=if p.withdrawal{0}else{1};pos+=1;
 if !p.withdrawal {fields(&mut out,&mut pos,&p.recipient)?;}
 fields(&mut out,&mut pos,&p.change)?;out[pos]=if p.withdrawal{1}else{0};pos+=1;
 if p.withdrawal {fields(&mut out,&mut pos,&[p.withdrawal_amount])?;}
 out[pos]=(p.next_pair_index>>0u32) as u8;pos+=1;out[pos]=(p.next_pair_index>>8u32) as u8;pos+=1;out[pos]=(p.next_pair_index>>16u32) as u8;pos+=1;out[pos]=(p.next_pair_index>>24u32) as u8;pos+=1;out[pos]=(p.next_pair_index>>32u32) as u8;pos+=1;out[pos]=(p.next_pair_index>>40u32) as u8;pos+=1;out[pos]=(p.next_pair_index>>48u32) as u8;pos+=1;out[pos]=(p.next_pair_index>>56u32) as u8;pos+=1;
 fields(&mut out,&mut pos,&p.frontier[0])?;
fields(&mut out,&mut pos,&p.frontier[1])?;
fields(&mut out,&mut pos,&p.frontier[2])?;
fields(&mut out,&mut pos,&p.frontier[3])?;
fields(&mut out,&mut pos,&p.frontier[4])?;
fields(&mut out,&mut pos,&p.frontier[5])?;
fields(&mut out,&mut pos,&p.frontier[6])?;
fields(&mut out,&mut pos,&p.frontier[7])?;
fields(&mut out,&mut pos,&p.frontier[8])?;
fields(&mut out,&mut pos,&p.frontier[9])?;
fields(&mut out,&mut pos,&p.frontier[10])?;
fields(&mut out,&mut pos,&p.frontier[11])?;
fields(&mut out,&mut pos,&p.frontier[12])?;
fields(&mut out,&mut pos,&p.frontier[13])?;
fields(&mut out,&mut pos,&p.frontier[14])?;
fields(&mut out,&mut pos,&p.frontier[15])?;
fields(&mut out,&mut pos,&p.frontier[16])?;
fields(&mut out,&mut pos,&p.frontier[17])?;
fields(&mut out,&mut pos,&p.frontier[18])?;
fields(&mut out,&mut pos,&p.frontier[19])?;
 fields(&mut out,&mut pos,&p.next_root)?;
 fields(&mut out,&mut pos,&p.next_frontier[0])?;
fields(&mut out,&mut pos,&p.next_frontier[1])?;
fields(&mut out,&mut pos,&p.next_frontier[2])?;
fields(&mut out,&mut pos,&p.next_frontier[3])?;
fields(&mut out,&mut pos,&p.next_frontier[4])?;
fields(&mut out,&mut pos,&p.next_frontier[5])?;
fields(&mut out,&mut pos,&p.next_frontier[6])?;
fields(&mut out,&mut pos,&p.next_frontier[7])?;
fields(&mut out,&mut pos,&p.next_frontier[8])?;
fields(&mut out,&mut pos,&p.next_frontier[9])?;
fields(&mut out,&mut pos,&p.next_frontier[10])?;
fields(&mut out,&mut pos,&p.next_frontier[11])?;
fields(&mut out,&mut pos,&p.next_frontier[12])?;
fields(&mut out,&mut pos,&p.next_frontier[13])?;
fields(&mut out,&mut pos,&p.next_frontier[14])?;
fields(&mut out,&mut pos,&p.next_frontier[15])?;
fields(&mut out,&mut pos,&p.next_frontier[16])?;
fields(&mut out,&mut pos,&p.next_frontier[17])?;
fields(&mut out,&mut pos,&p.next_frontier[18])?;
fields(&mut out,&mut pos,&p.next_frontier[19])?;
 Ok((out,pos))
}
