#![no_std]
extern crate alloc;
use core::mem::MaybeUninit;
use alloc::boxed::Box;
#[kani::proof]
fn scalar_control(){let x=kani::any::<u32>();assert!(x==x);}
#[kani::proof]
fn stack_uninit(){let mut x=MaybeUninit::<u32>::uninit(); x.write(5);assert!(unsafe{x.assume_init()}==5);}
#[kani::proof]
fn box_uninit(){let mut x=Box::new(MaybeUninit::<u32>::uninit());x.write(5);assert!(unsafe{x.assume_init()}==Box::new(5));}
