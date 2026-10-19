use core::ops::ControlFlow;
use core::convert::Infallible;
pub trait BorrowTry<'a,T> {
    fn branch(self) -> ControlFlow<Option<Infallible>, &'a mut T>;
}
impl<'a,T> BorrowTry<'a,T> for Option<&'a mut T> {
    fn branch(self) -> ControlFlow<Option<Infallible>, &'a mut T> {
        match self {
            Some(v) => ControlFlow::Continue(v),
            None => ControlFlow::Break(None),
        }
    }
}
pub fn from_residual<'a,T>(residual:Option<Infallible>) -> Option<(usize,&'a mut T)> {
        match residual {
            None => None,
        }
    }
