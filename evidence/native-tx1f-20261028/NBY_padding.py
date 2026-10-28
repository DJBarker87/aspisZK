import NBY_generate as g
body='''let proof:[u8;57607]=kani::any();let s:usize=kani::any();let count:usize=kani::any();kani::assume(s<6&&count<=SLOT_NODES[s]);let nodes=slot(&proof,s);let padding=&nodes[32*count..];let mut it=padding.chunks_exact(8);let before=it.len();let first=it.next();'''
g.pair('padding_physical_iterator',body,'''before==4*(SLOT_NODES[s]-count)&&it.remainder().is_empty()&&match first{Some(w)=>w.len()==8&&w.as_ptr()==nodes.as_ptr().wrapping_add(32*count)&&it.len()==before-1,None=>count==SLOT_NODES[s]}''')
body='''let nodes:[u8;5504]=kani::any();let cap:usize=kani::any();let count:usize=kani::any();let j:usize=kani::any();kani::assume(count<=cap&&cap<=172&&j<=4*(cap-count));let at=32*count+8*j;let mut it=nodes[at..32*cap].chunks_exact(8);let out=it.next();'''
g.pair('padding_arbitrary_cursor',body,'''match out{Some(w)=>j<4*(cap-count)&&w.as_ptr()==nodes.as_ptr().wrapping_add(at)&&w.len()==8&&it.len()==4*(cap-count)-j-1,None=>j==4*(cap-count)}''')
body='''let proof:[u8;57607]=kani::any();let s:usize=kani::any();let count:usize=kani::any();kani::assume(s<6&&count>SLOT_NODES[s]);let nodes=slot(&proof,s);let mut scans=0usize;let result:Result<(),Error>=if count>SLOT_NODES[s]{Err(Error::Parse)}else{scans+=1;let _padding=&nodes[32*count..];Ok(())};'''
g.pair('padding_capacity_short_circuit',body,'matches!(result,Err(Error::Parse))&&scans==0')
body='''let word:[u8;8]=kani::any();let before:bool=kani::any();let mut it=word.chunks_exact(8);let w=it.next().unwrap();let nonzero=u64::from_le_bytes(w.try_into().unwrap())!=0;let mut calls=0;let result:Result<(),Error>=if nonzero{Err(Error::Parse)}else{calls+=1;if before{Ok(())}else{Err(Error::Merkle)}};'''
g.pair('padding_word_continuation',body,'nonzero==word.iter().any(|&b|b!=0)&&calls==usize::from(!nonzero)&&result.is_ok()==(!nonzero&&before)')
body='''let proof:[u8;57607]=kani::any();let s:usize=kani::any();kani::assume(s<6);let count=SLOT_NODES[s];let nodes=slot(&proof,s);let mut it=nodes[32*count..].chunks_exact(8);let next=it.next();let checked=it.remainder();'''
g.pair('padding_exact_end',body,'next.is_none()&&checked.is_empty()&&it.len()==0&&count*32==nodes.len()')
body='''let bytes:[u8;32]=kani::any();let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<4&&k<32);let old=bytes[k];let mut it=bytes[8*j..].chunks_exact(8);let w=it.next().unwrap();let nonzero=u64::from_le_bytes(w.try_into().unwrap())!=0;'''
g.pair('padding_local_read_frame',body,'bytes[k]==old&&nonzero==(0..8).any(|c|bytes[8*j+c]!=0)&&it.len()==3-j')
if __name__=='__main__':g.publish('NBY_padding','candidate.rs',53)
