#[derive(Clone)]
pub enum ProgramError{Custom(u32),InvalidArgument,InvalidInstructionData,InvalidAccountData,AccountDataTooSmall,InsufficientFunds,IncorrectProgramId,MissingRequiredSignature,AccountAlreadyInitialized,UninitializedAccount,NotEnoughAccountKeys,AccountBorrowFailed,MaxSeedLengthExceeded,InvalidSeeds,BorshIoError(String),AccountNotRentExempt,UnsupportedSysvar,IllegalOwner,MaxAccountsDataAllocationsExceeded,InvalidRealloc,MaxInstructionTraceLengthExceeded,BuiltinProgramsMustConsumeComputeUnits,InvalidAccountOwner,ArithmeticOverflow,Immutable,IncorrectAuthority}
pub struct OwnedAccount{pub key:[u8;32],pub owner:[u8;32],pub is_signer:bool,pub is_writable:bool,pub executable:bool,pub length:Result<usize,ProgramError>,pub bytes:Result<Vec<u8>,ProgramError>}
pub fn snapshot_ref(key:[u8;32],owner:[u8;32],is_signer:bool,is_writable:bool,executable:bool,length1:usize,length2:usize,borrowed:Result<&[u8],ProgramError>)->OwnedAccount{
 let (length,bytes)=match borrowed{
  Ok(data)=>{let length=data.len();let bytes=if length==length1||length==length2{Ok(data.to_vec())}else{Err(ProgramError::InvalidAccountData)};(Ok(length),bytes)}
  Err(error)=>(Err(error.clone()),Err(error)),
 };
 OwnedAccount{key,owner,is_signer,is_writable,executable,length,bytes}
}
