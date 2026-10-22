#![allow(unexpected_cfgs)]
pub mod field;pub mod r0;
use field::WideExact as E;
pub fn eval(q:&[E;1024],x:E,y:E)->E {
 r0::encoder::eval_message(q,r0::domain::Point{x,y})
}
