use block_buffer::pv_rl_split;
fn copy_range(data:&[u8],start:usize,end:usize,out:&mut Vec<u8>){
 let mut i=start;while i<end{out.push(data[i]);i+=1;}
}
fn split_flat_reference(data:&[u8],size:usize,blocks:&mut Vec<u8>,tail:&mut Vec<u8>){
 let count=data.len()/size;let consumed=count*size;
 copy_range(data,0,consumed,blocks);copy_range(data,consumed,data.len(),tail);
}
fn check(data:&[u8]){
 let (b,t)=pv_rl_split(data);let mut rb=Vec::new();let mut rt=Vec::new();
 split_flat_reference(data,64,&mut rb,&mut rt);
 assert_eq!(std::mem::size_of_val(b),rb.len());assert_eq!(t,rt);
 for (i,c) in b.iter().enumerate(){assert_eq!(&c[..],&rb[i*64..(i+1)*64]);}
 assert_eq!(t.as_ptr(),unsafe{data.as_ptr().add(rb.len())});
 if !b.is_empty(){assert_eq!(b.as_ptr().cast::<u8>(),data.as_ptr());}
}
fn main(){
 assert_eq!(std::mem::size_of::<block_buffer::Block<block_buffer::generic_array::typenum::U64>>(),64);
 assert_eq!(std::mem::align_of::<block_buffer::Block<block_buffer::generic_array::typenum::U64>>(),1);
 let mut cases=0u64;
 for seed in 0..8usize{
 let data:Vec<u8>=(0..4097).map(|i|((i*17+seed*31+(i>>8))%256)as u8).collect();
 for n in 0..=4097 {check(&data[..n]);cases+=1;}
 }
 for a in 0..=255 {let data=vec![a;129];for n in 0..=129{check(&data[..n]);cases+=1;}}
 println!("V233 finite validation: {cases} same-input comparisons; every block byte, tail byte, count and alias pointer; no disagreement");}
