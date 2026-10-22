pub mod scalar;pub use scalar::CodeField;pub mod basis;pub mod encoder;pub type Message<E>=[E;1024];
pub mod domain {#[derive(Clone,Copy)] pub struct Point<E>{pub x:E,pub y:E}}
