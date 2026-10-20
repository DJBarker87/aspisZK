#![no_std]

pub mod aspis_core {
    pub mod r0 {
        pub const MESSAGE_LEN: usize = 1024;
        pub type Message<E> = [E; MESSAGE_LEN];
        pub mod transport;
    }
}

pub mod transport;
