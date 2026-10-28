#[derive(Clone,Copy)]
pub enum TerminalView<P,W,T>{Transfer(P,T),Withdrawal(W,T)}
pub fn terminal_view_ref<P:Copy,W:Copy,T:Copy>(v:TerminalView<P,W,T>)->TerminalView<P,W,T>{match v{TerminalView::Transfer(p,t)=>TerminalView::Transfer(p,t),TerminalView::Withdrawal(w,t)=>TerminalView::Withdrawal(w,t)}}
