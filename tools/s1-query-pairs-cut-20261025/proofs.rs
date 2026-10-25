fn owned_contains(a:&[u32;22],len:usize,candidate:u32)->bool{
 let mut j=0;while j<len{if a[j]==candidate{return true;}j+=1;}false
}
fn owned_step(mut a:[u32;22],mut len:usize,mut draws:usize,candidate:u32)->([u32;22],usize,usize,bool){
 if len==22 || draws==64{return(a,len,draws,true);}
 draws+=1;
 if !owned_contains(&a,len,candidate){a[len]=candidate;len+=1;}
 (a,len,draws,false)
}
fn owned_block(mut accepted:[u32;22],mut len:usize,mut draws:usize,block:&[u8;32])->([u32;22],usize,usize,bool){
 let mut i=0;
 while i<8{
  let off=4*i;let candidate=u32::from_le_bytes([block[off],block[off+1],block[off+2],block[off+3]])&((1u32<<18)-1);
  let (a,n,d,stop)=owned_step(accepted,len,draws,candidate);
  accepted=a;len=n;draws=d;
  if stop{return(accepted,len,draws,true);}
  i+=1;
 }
 (accepted,len,draws,false)
}

struct OwnedScan{accepted:[u32;22],accepted_len:usize,draws:usize}
fn pairs_step(scan:OwnedScan,state:[u8;32],k:usize,blocks:&[[u8;32];8],advances:&[[u8;32];8])->(OwnedScan,[u8;32],bool){
 let (a,n,d,stop)=owned_block(scan.accepted,scan.accepted_len,scan.draws,&blocks[k]);
 let after=OwnedScan{accepted:a,accepted_len:n,draws:d};
 if stop{(after,advances[k],true)}else{(after,state,false)}
}
fn pairs_finish(scan:OwnedScan,state:[u8;32])->Result<([u32;22],[u8;32]),QuerySampleError>{
 if scan.accepted_len==22{Ok((scan.accepted,state))}
 else{Err(QuerySampleError::DrawLimitExhausted{accepted:scan.accepted_len,max_draws:64})}
}
fn pairs_reference(blocks:&[[u8;32];8],advances:&[[u8;32];8])->Result<([u32;22],[u8;32]),QuerySampleError>{
 let scan=OwnedScan{accepted:[0;22],accepted_len:0,draws:0};let state=advances[7];
 let (scan,state,stop)=pairs_step(scan,state,0,blocks,advances);
 if stop{return pairs_finish(scan,state);}
 let (scan,state,stop)=pairs_step(scan,state,1,blocks,advances);
 if stop{return pairs_finish(scan,state);}
 let (scan,state,stop)=pairs_step(scan,state,2,blocks,advances);
 if stop{return pairs_finish(scan,state);}
 let (scan,state,stop)=pairs_step(scan,state,3,blocks,advances);
 if stop{return pairs_finish(scan,state);}
 let (scan,state,stop)=pairs_step(scan,state,4,blocks,advances);
 if stop{return pairs_finish(scan,state);}
 let (scan,state,stop)=pairs_step(scan,state,5,blocks,advances);
 if stop{return pairs_finish(scan,state);}
 let (scan,state,stop)=pairs_step(scan,state,6,blocks,advances);
 if stop{return pairs_finish(scan,state);}
 let (scan,state,stop)=pairs_step(scan,state,7,blocks,advances);
 let _=stop; pairs_finish(scan,state)
}
#[kani::proof]#[kani::unwind(34)]
#[kani::stub(super::QueryScan::scan,super::s126_scan_reply)]
#[kani::stub(owned_block,super::s126_reference_scan_reply)]
fn pairs_cut_equal(){
 let blocks=kani::any::<[[u8;32];8]>();let advances=kani::any::<[[u8;32];8]>();
 let tape=kani::any::<[S126Reply;8]>();let mut i=0;
 while i<8{kani::assume(tape[i].1<=22);kani::assume(tape[i].2<=64);i+=1;}
 let call=kani::any::<usize>();let word=kani::any::<usize>();let byte=kani::any::<usize>();
 kani::assume(call<8);kani::assume(word<22);kani::assume(byte<32);
 s126_init(tape,call,word,byte);
 let actual=super::queries_from_pairs(&blocks,&advances);
 let reference=pairs_reference(&blocks,&advances);
 match(actual,reference){
  (Ok((a,s)),Ok((b,t)))=>{assert!(a[word]==b[word]);assert!(s[byte]==t[byte]);kani::cover!(true,"both accepted");},
  (Err(a),Err(b))=>{assert!(a==b);kani::cover!(true,"both rejected");},
  _=>assert!(false,"native complete Result mismatch"),
 }
 let (actual_calls,reference_calls)=s126_counts();assert!(actual_calls==reference_calls);
 kani::cover!(actual_calls==8,"all eight native scan calls");
}
