// Owned safe library specification. Heap identities are indices, not integer
// pointer encodings. Native-to-carrier interpretation is a separate obligation.
// Guard is not Clone/Copy; acquisition returns it once and drop consumes it.
pub struct Cell { pub counter:i64, pub data:Vec<u8> }
pub struct Account { pub cell:usize, pub key:[u8;32], pub owner:[u8;32], pub lamports:u64, pub signer:bool, pub writable:bool, pub executable:bool, pub rent_epoch:u64 }
pub struct Heap { pub accounts:[Account;7], pub cells:[Cell;7], pub count:usize }
pub struct Guard { pub cell:usize, pub exclusive:bool }
pub enum BorrowReply { Ok(Guard), AccountBorrowFailed }
pub struct BorrowOutput { pub heap:Heap, pub reply:BorrowReply }
pub fn borrow_ref(mut heap:Heap, account:usize, exclusive:bool)->BorrowOutput {
    let cell=heap.accounts[account].cell;
    let old=heap.cells[cell].counter;
    let allowed=if exclusive { old==0 } else { old>=0 && old<i64::MAX };
    if allowed {
        heap.cells[cell].counter=if exclusive {-1} else {old+1};
        BorrowOutput{heap,reply:BorrowReply::Ok(Guard{cell,exclusive})}
    } else { BorrowOutput{heap,reply:BorrowReply::AccountBorrowFailed} }
}
pub fn deref_ref<'a>(heap:&'a Heap,guard:&Guard)->&'a [u8] { &heap.cells[guard.cell].data }
pub fn deref_mut_ref<'a>(heap:&'a mut Heap,guard:&Guard)->&'a mut [u8] { &mut heap.cells[guard.cell].data }
pub fn drop_ref(mut heap:Heap, guard:Guard)->Heap {
    let cell=guard.cell;
    heap.cells[cell].counter=if guard.exclusive {heap.cells[cell].counter+1} else {heap.cells[cell].counter-1};
    heap
}
pub fn copy_coordinate_ref(mut heap:Heap, guard:&Guard, index:usize, value:u8)->Heap {
    heap.cells[guard.cell].data[index]=value; heap
}
pub struct Clock { pub slot:u64, pub epoch_start_timestamp:i64, pub epoch:u64, pub leader_schedule_epoch:u64, pub unix_timestamp:i64 }
// Exact injective representation of ProgramError: kind=1..26 for built-ins;
// kind=0 Custom(custom); kind=15 is BorshIoError("Unknown") in this converter.
pub struct ProgramError { pub kind:u32, pub custom:u32 }
pub fn program_error_ref(status:u64)->ProgramError {
    let tag=status>>32;
    if status==1u64<<32 {ProgramError{kind:0,custom:0}}
    else if (status&0xffff_ffff)==0 && tag>=2 && tag<=26 {ProgramError{kind:tag as u32,custom:0}}
    else {ProgramError{kind:0,custom:status as u32}}
}
pub enum ClockReply { Ok(Clock), Err(ProgramError) }
pub fn clock_ref(status:u64, output:Clock)->ClockReply {
    if status==0 {ClockReply::Ok(output)} else {ClockReply::Err(program_error_ref(status))}
}
pub enum PdaReply { Ok([u8;32]), MaxSeedLengthExceeded, InvalidSeeds, IllegalOwner, Abort }
pub fn pda_status_ref(status:u64, output:[u8;32])->PdaReply {
    if status==0 {PdaReply::Ok(output)} else if status==1 {PdaReply::InvalidSeeds}
    else if status==2 {PdaReply::IllegalOwner} else {PdaReply::Abort}
}
pub struct PdaInput { pub seeds:Vec<Vec<u8>>, pub program_id:[u8;32] }
pub struct PdaOutput { pub input:PdaInput, pub status:u64, pub output:[u8;32], pub called:bool, pub reply:PdaReply }
pub fn seed_lengths_ref(input:&PdaInput)->bool {
    if input.seeds.len()>16 {return false;}
    for seed in input.seeds.iter() {if seed.len()>32 {return false;}}
    true
}
pub fn pda_ref(input:PdaInput,status:u64,output:[u8;32])->PdaOutput {
    if seed_lengths_ref(&input) {
        PdaOutput{input,status,output,called:true,reply:pda_status_ref(status,output)}
    } else {PdaOutput{input,status,output,called:false,reply:PdaReply::MaxSeedLengthExceeded}}
}
pub fn guard_move_ref(guard:Guard)->Guard {guard}
pub fn error_drop_ref(heap:Heap)->Heap {heap}
