
#[cfg(kani)]
mod PoolN_dispatch {
use super::*;
fn PoolN_route(data:&[u8])->Result<u8,ProgramError> {
let magic=data.get(..4).ok_or(ProgramError::InvalidInstructionData)?;
if cfg!(feature = "pair-forest-account-evidence") && magic == b"AS8I" { Ok(0) }
else if cfg!(feature = "pair-forest-account-evidence") && magic == b"AS8C" { Ok(1) }
else if cfg!(feature = "pair-forest-account-evidence") && magic == b"AS8D" { Ok(2) }
else if cfg!(feature = "pair-forest-account-evidence") && magic == b"ASQ8" { Ok(3) }
else if cfg!(feature = "pair-forest-full-asf8-audit") && magic == b"ASF8" { Ok(4) }
else if magic == POOL_V1_INITIALIZE_INSTRUCTION_MAGIC { Ok(5) }
else if magic == POOL_V1_DEPOSIT_INSTRUCTION_MAGIC { Ok(6) }
else if magic == POOL_V1_PREPARE_SETTLEMENT_INSTRUCTION_MAGIC { Ok(7) }
else if magic == POOL_V1_CANCEL_PREPARED_SETTLEMENT_INSTRUCTION_MAGIC { Ok(8) }
else if magic == POOL_V1_SETTLE_PREPARED_INSTRUCTION_MAGIC { Ok(9) }
else if cfg!(feature = "pair-afterstate-evidence")
        && magic == crate::instruction::POOL_V1_PAIR_PRIVATE_TRANSFER_INSTRUCTION_MAGIC { Ok(10) }
else if cfg!(feature = "pair-afterstate-evidence")
        && magic == crate::instruction::POOL_V1_PAIR_WITHDRAWAL_INSTRUCTION_MAGIC { Ok(11) }
else if magic == POOL_V1_PRIVATE_TRANSFER_INSTRUCTION_MAGIC { Ok(12) }
else if magic == POOL_V1_WITHDRAWAL_INSTRUCTION_MAGIC { Ok(13) }
else {Err(ProgramError::InvalidInstructionData)}
}
#[kani::proof]
#[kani::unwind(18)]
fn PoolN_dispatch_projection() {
 let data:[u8;4]=kani::any();let result=PoolN_route(&data);
 assert!(!matches!(result,Ok(4|10|11)));
 assert_eq!(PoolN_route(b"AS8I"),Ok(0));
 kani::cover!(PoolN_route(b"AS8I")==Ok(0),"AS8I route reachable");
 assert_eq!(PoolN_route(b"AS8C"),Ok(1));
 kani::cover!(PoolN_route(b"AS8C")==Ok(1),"AS8C route reachable");
 assert_eq!(PoolN_route(b"AS8D"),Ok(2));
 kani::cover!(PoolN_route(b"AS8D")==Ok(2),"AS8D route reachable");
 assert_eq!(PoolN_route(b"ASQ8"),Ok(3));
 kani::cover!(PoolN_route(b"ASQ8")==Ok(3),"ASQ8 route reachable");
 assert_eq!(PoolN_route(b"ASIN"),Ok(5));
 kani::cover!(PoolN_route(b"ASIN")==Ok(5),"ASIN route reachable");
 assert_eq!(PoolN_route(b"ASDI"),Ok(6));
 kani::cover!(PoolN_route(b"ASDI")==Ok(6),"ASDI route reachable");
 assert_eq!(PoolN_route(b"ASPP"),Ok(7));
 kani::cover!(PoolN_route(b"ASPP")==Ok(7),"ASPP route reachable");
 assert_eq!(PoolN_route(b"ASPX"),Ok(8));
 kani::cover!(PoolN_route(b"ASPX")==Ok(8),"ASPX route reachable");
 assert_eq!(PoolN_route(b"ASPF"),Ok(9));
 kani::cover!(PoolN_route(b"ASPF")==Ok(9),"ASPF route reachable");
 assert_eq!(PoolN_route(b"ASPT"),Ok(12));
 kani::cover!(PoolN_route(b"ASPT")==Ok(12),"ASPT route reachable");
 assert_eq!(PoolN_route(b"ASWD"),Ok(13));
 kani::cover!(PoolN_route(b"ASWD")==Ok(13),"ASWD route reachable");
 assert_eq!(PoolN_route(b"ASF8"),Err(ProgramError::InvalidInstructionData));
 assert_eq!(PoolN_route(b"ASJP"),Err(ProgramError::InvalidInstructionData));
 assert_eq!(PoolN_route(b"ASJW"),Err(ProgramError::InvalidInstructionData));
 if &data != b"AS8I" && &data != b"AS8C" && &data != b"AS8D" && &data != b"ASQ8" && &data != b"ASIN" && &data != b"ASDI" && &data != b"ASPP" && &data != b"ASPX" && &data != b"ASPF" && &data != b"ASPT" && &data != b"ASWD" {assert_eq!(result,Err(ProgramError::InvalidInstructionData));}
}
}
