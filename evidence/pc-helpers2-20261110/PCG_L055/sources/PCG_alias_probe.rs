use std::cell::Cell;
#[repr(C)] struct Context { program:[u8;32], reply:[u8;32], calls:Cell<u8> }
#[inline(never)] unsafe fn oracle(program:*const u8)->[u8;32]{let c=&*(program as *const Context);c.calls.set(c.calls.get()+1);c.reply}
#[inline(never)] fn wrapper(program:&[u8;32])->[u8;32]{unsafe{oracle(program as *const _ as *const u8)}}
fn main(){let c=Context{program:[11;32],reply:[37;32],calls:Cell::new(0)};assert_eq!(wrapper(&c.program),[37;32]);assert_eq!(c.calls.get(),1);}
