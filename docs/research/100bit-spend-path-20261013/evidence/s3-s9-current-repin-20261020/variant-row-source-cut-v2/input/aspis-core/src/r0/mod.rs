pub const MESSAGE_LEN: usize = 1024;
pub type Message<E> = [E; MESSAGE_LEN];
pub mod transport;
