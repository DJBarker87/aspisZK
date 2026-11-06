// Parent probes call the actual frozen functions directly.
// Segment starts at the returned Option of the SAME node_count call.
fn count_return_fragment(counted:Option<usize>)->Result<usize,Error>{
 let count=counted.ok_or(Error::Merkle)?;
 Ok(count)
}
fn prefix_size_fragment(count:usize)->usize {32 * count}

// Call-site ghosts erase to the verbatim frozen four-statement entry block.
// Closures forward unchanged arguments to the original qualified helpers.
#[derive(Default)]
struct KeyArgsLog {calls:usize,order:usize,queries:[u32;22],lo:usize,n:usize,tree:usize,reply:[u64;16]}
#[derive(Default)]
struct SortArgsLog {calls:usize,order:usize,input:[u64;16],n:usize,reply:[u64;16]}
#[derive(Default)]
struct KeyEntryLog {key:KeyArgsLog,sort:SortArgsLog,count:usize}
fn key_entry_fragment(queries:[u32;22],batch:usize,tree:usize,log:&mut KeyEntryLog)->(usize,usize,usize,[u64;16]){
 let counter=core::cell::Cell::new(0usize);
 let key_log=&mut log.key;let sort_log=&mut log.sort;
 let mut batch_keys=|queries:&[u32;22],lo:usize,n:usize,tree:usize|{
  key_log.calls+=1;key_log.order=counter.get();counter.set(counter.get()+1);
  key_log.queries=*queries;key_log.lo=lo;key_log.n=n;key_log.tree=tree;
  let reply=super::batch_keys(queries,lo,n,tree);key_log.reply=reply;reply
 };
 let mut sort_batch_keys=|raw:[u64;16],n:usize|{
  sort_log.calls+=1;sort_log.order=counter.get();counter.set(counter.get()+1);
  sort_log.input=raw;sort_log.n=n;
  let reply=super::sort_batch_keys(raw,n);sort_log.reply=reply;reply
 };
    let (lo, hi) = if batch == 0 { (0, SPLIT) } else { (SPLIT, 22) };
    let n = hi - lo;
    let s = 3 * batch + tree;
    let keys = sort_batch_keys(batch_keys(&queries, lo, n, tree), n);
 log.count=counter.get();(lo,n,s,keys)
}
fn key_reply(_queries:&[u32;22],_lo:usize,_n:usize,_tree:usize)->[u64;16]{kani::any()}
fn sort_reply(_raw:[u64;16],_n:usize)->[u64;16]{kani::any()}
#[kani::proof]
#[kani::unwind(64)]
#[kani::stub(super::batch_keys,key_reply)]
#[kani::stub(super::sort_batch_keys,sort_reply)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn key_entry(){
 let queries:[u32;22]=kani::any();let batch:usize=kani::any();let tree:usize=kani::any();kani::assume(batch<2&&tree<3);
 let mut log=KeyEntryLog::default();let (lo,n,s,keys)=key_entry_fragment(queries,batch,tree,&mut log);
 let expected_lo=if batch==0{0}else{10};let expected_n=if batch==0{10}else{12};
 assert!(lo==expected_lo&&n==expected_n&&s==3*batch+tree&&s<6);
 assert!(log.count==2&&log.key.calls==1&&log.sort.calls==1&&log.key.order==0&&log.sort.order==1);
 assert!(log.key.lo==lo&&log.key.n==n&&log.key.tree==tree&&log.sort.n==n);
 let j:usize=kani::any();let qi:usize=kani::any();kani::assume(j<16&&qi<22);
 #[cfg(not(NKV_copy_control))] assert!(log.key.queries[qi]==queries[qi]);
 #[cfg(NKV_copy_control)] assert!(log.key.queries[qi]!=queries[qi]);
 assert!(log.sort.input[j]==log.key.reply[j]);
 #[cfg(not(NKV_invert))] assert!(keys[j]==log.sort.reply[j]);
 #[cfg(NKV_invert)] assert!(keys[j]!=log.sort.reply[j]);
}
