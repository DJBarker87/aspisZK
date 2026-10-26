
#[cfg(kani)]
mod PoolN_stack {
use super::*;
use solana_program::instruction::TRANSACTION_LEVEL_STACK_HEIGHT;
fn PoolN_stack_gate(stack_height: usize) -> ProgramResult {
    if stack_height != TRANSACTION_LEVEL_STACK_HEIGHT {
        return Err(PoolV1ProgramError::CpiInvocationForbidden.into());
    }
    Ok(())
}
#[kani::proof]
fn PoolN_stack_no_inner_invocation() {
 let height:usize=kani::any();
 let expected=if height==TRANSACTION_LEVEL_STACK_HEIGHT {Ok(())} else {Err(PoolV1ProgramError::CpiInvocationForbidden.into())};
 assert_eq!(PoolN_stack_gate(height),expected);
 kani::cover!(PoolN_stack_gate(TRANSACTION_LEVEL_STACK_HEIGHT).is_ok(),"transaction admitted");
 kani::cover!(PoolN_stack_gate(TRANSACTION_LEVEL_STACK_HEIGHT+1).is_err(),"CPI rejected");
}
}
