pub struct Token(pub u64);
pub fn reborrow<'a,'b>(pending:&'a mut Option<&'b mut Token>)->Option<&'a mut Token>{pending.as_deref_mut()}
