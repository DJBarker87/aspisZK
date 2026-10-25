
// Proof-only private-state access; original QueryScan and scan body unchanged.
#[cfg(kani)]
pub fn s126_scan_block(accepted:[u32;22],accepted_len:usize,draws:usize,block:&[u8;32])->([u32;22],usize,usize,bool){
 let mut scan=QueryScan{accepted,accepted_len,draws};let stop=scan.scan(block);
 (scan.accepted,scan.accepted_len,scan.draws,stop)
}
