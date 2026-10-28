use std::{path::Path,os::unix::ffi::OsStrExt};
fn string_owned_reference(s:String)->String {s}
fn check(s:String){
 let p:&Path=s.as_ref();assert_eq!(p.as_os_str().as_bytes(),s.as_bytes());
 if !s.is_empty(){assert_eq!(p.as_os_str().as_bytes().as_ptr(),s.as_bytes().as_ptr());}
 let before=s.as_bytes().to_vec();let r=string_owned_reference(s);assert_eq!(before,r.as_bytes());
}
fn main(){let mut cases=0u64;check(String::new());cases+=1;
 for n in 0..=0x10ffff {if let Some(c)=char::from_u32(n){let s=c.to_string();check(s.clone());check(format!("a{c}/\0..{c}"));cases+=2;}}
 for n in [2,3,8,16,64,129,1025]{check("é/\0🦀".repeat(n));cases+=1;}
 println!("V179 finite validation: {cases} same-input comparisons; all Unicode scalar values plus contextual strings; no disagreement");}
