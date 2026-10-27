fn PoolV_zero(bytes:&[u8])->bool {
    let mut i=0;let mut zero=true;
    while i<bytes.len() && zero { zero=bytes[i]==0;i+=1; }
    zero
}
#[kani::proof]
#[kani::unwind(195)]
fn PoolV_zero_native_p6() {
    let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
    let mut bytes:[u8;192]=kani::any();let mut funds:u64=kani::any();let old=funds;
    let selected:usize=kani::any();kani::assume(selected<192);let before=bytes[selected];
    let zero=PoolV_zero(&bytes);let rent=Rent::default();
    let expected=if zero && rent.is_exempt(funds,192){Ok(())}else{Err(PoolV1ProgramError::InvalidFreshAccount.into())};
    let a=AccountInfo::new(&key,kani::any(),true,&mut funds,&mut bytes,&id,false,kani::any());
    assert!(require_program_owned_zeroed(&a,&id,192,&rent)==expected);
    assert!(a.try_borrow_mut_data().is_ok());drop(a);
    assert!(bytes[selected]==before && funds==old);
}
#[kani::proof]
#[kani::unwind(195)]
fn PoolV_fresh_native_p6() {
    let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
    let mut bytes:[u8;192]=kani::any();let mut funds:u64=kani::any();let old=funds;
    let selected:usize=kani::any();kani::assume(selected<192);let before=bytes[selected];
    let expected=if PoolV_zero(&bytes){Ok(FreshPdaPreparationV1::ProgramOwnedZeroed)}else{Err(PoolV1ProgramError::InvalidFreshAccount.into())};
    let a=AccountInfo::new(&key,false,true,&mut funds,&mut bytes,&id,false,kani::any());
    assert!(plan_fresh_program_pda(&a,&id,&key,192)==expected);
    assert!(a.try_borrow_mut_data().is_ok());drop(a);
    assert!(bytes[selected]==before && funds==old);
}
fn PoolV_copy_conflict(checkpoint_conflict:bool){
    let id=Pubkey::new_from_array([7;32]);let mk=Pubkey::new_from_array([8;32]);let ck=Pubkey::new_from_array([9;32]);
    let mut m:[u8;384]=kani::any();let mut c:[u8;192]=kani::any();let mut ml:u64=kani::any();let mut cl:u64=kani::any();let oldml=ml;let oldcl=cl;
    let i:usize=kani::any();kani::assume(i<384);let j:usize=kani::any();kani::assume(j<192);let mb=m[i];let cb=c[j];
    let plan=PoolV_Planned{checkpoint_image:kani::any(),next_master_image:kani::any()};
    let master=AccountInfo::new(&mk,false,true,&mut ml,&mut m,&id,false,0);
    let checkpoint=AccountInfo::new(&ck,false,true,&mut cl,&mut c,&id,false,0);
    let held=if checkpoint_conflict {checkpoint.try_borrow_data().unwrap()}else{master.try_borrow_data().unwrap()};
    assert!(PoolV_copy_tail(&master,&checkpoint,&plan)==Err(ProgramError::AccountBorrowFailed));drop(held);
    assert!(master.try_borrow_mut_data().is_ok());assert!(checkpoint.try_borrow_mut_data().is_ok());
    drop(master);drop(checkpoint);assert!(m[i]==mb && c[j]==cb && ml==oldml && cl==oldcl);
}
#[kani::proof]
#[kani::unwind(80)]
fn PoolV_copy_master_error(){PoolV_copy_conflict(false);}
#[kani::proof]
#[kani::unwind(80)]
fn PoolV_copy_checkpoint_error(){PoolV_copy_conflict(true);}
#[kani::proof]
#[kani::unwind(80)]
fn PoolV_zero_read_error(){
    let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
    let mut bytes:[u8;192]=kani::any();let mut funds:u64=kani::any();let old=funds;
    let i:usize=kani::any();kani::assume(i<192);let before=bytes[i];
    let a=AccountInfo::new(&key,kani::any(),true,&mut funds,&mut bytes,&id,false,0);
    let held=a.try_borrow_mut_data().unwrap();
    assert!(require_program_owned_zeroed(&a,&id,192,&Rent::default())==Err(ProgramError::AccountBorrowFailed));
    drop(held);assert!(a.try_borrow_mut_data().is_ok());drop(a);assert!(bytes[i]==before && funds==old);
}
