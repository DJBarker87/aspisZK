// Safe references for SDK scalar state transitions and full syscall reply carriers.
// These references do not assert a syscall value law or a pointer interpretation.
#[derive(Clone, Copy)]
pub struct Clock { pub slot:u64, pub epoch_start_timestamp:i64, pub epoch:u64, pub leader_schedule_epoch:u64, pub unix_timestamp:i64 }
pub fn shared_ref(counter:i64)->Result<i64,()> {
    if counter>=0 && counter<i64::MAX {Ok(counter+1)} else {Err(())}
}
pub fn exclusive_ref(counter:i64)->Result<i64,()> {
    if counter==0 {Ok(-1)} else {Err(())}
}
pub fn shared_drop_ref(counter:i64)->i64 {counter-1}
pub fn exclusive_drop_ref()->i64 {0}
pub fn copy_window_ref(old:u8,new:u8,index:usize,selected:usize)->u8 {
    if index==selected {new} else {old}
}
pub fn clock_ref(status:u64, clock:Clock)->Result<Clock,u64> {
    if status==0 {Ok(clock)} else {Err(status)}
}
pub fn pda_reply_ref(status:u64, bytes:[u8;32])->Result<[u8;32],u64> {
    if status==0 {Ok(bytes)} else {Err(status)}
}
