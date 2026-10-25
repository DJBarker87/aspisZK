
// Exact source single-word body, with only its self receiver bound to scan.
#[cfg(kani)] pub fn s126_scan_step(accepted:[u32;22],accepted_len:usize,draws:usize,candidate:u32)->([u32;22],usize,usize,bool){
 let mut scan=QueryScan{accepted,accepted_len,draws};
 let stop=(||{
            if scan.accepted_len == QUERY_COUNT || scan.draws == QUERY_MAX_DRAWS {
                return true;
            }
            scan.draws += 1;
            if !scan.accepted[..scan.accepted_len].contains(&candidate) {
                scan.accepted[scan.accepted_len] = candidate;
                scan.accepted_len += 1;
            }
 false})();
 (scan.accepted,scan.accepted_len,scan.draws,stop)
}
