#![crate_type="lib"]
use std::path::{Path,PathBuf};
pub fn take(v:&mut Vec<u8>)->Vec<u8>{std::mem::take(v)}
pub fn path_deref(p:&PathBuf)->&Path{p}
pub fn string_as_ref(p:&String)->&Path{p.as_ref()}
pub fn path_as_ref(p:&PathBuf)->&Path{p.as_ref()}
pub fn join(p:&Path,s:&Path)->PathBuf{p.join(s)}
pub fn string_capacity(n:usize)->String{String::with_capacity(n)}
pub fn push(p:&mut String,s:&str){p.push_str(s)}
pub fn empty(p:&Vec<u8>)->bool{p.is_empty()}
pub fn default_vec()->Vec<u8>{Vec::default()}
pub fn pop(p:&mut Vec<u32>)->Option<u32>{p.pop()}
pub fn array(p:Vec<u32>)->Result<[u32;32],Vec<u32>>{p.try_into()}
pub fn reserve(p:&mut Vec<u32>,n:usize)->Result<(),std::collections::TryReserveError>{p.try_reserve_exact(n)}
pub fn drop_vec(p:Vec<u32>){drop(p)}
