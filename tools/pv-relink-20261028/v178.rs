use std::{path::Path,ffi::OsStr,os::unix::ffi::OsStrExt};
// Exact owned reference from tools/pv-cblib-20261027/lib.rs; checked by bind-v178.py.
fn join_slices_reference(base:&[u8],path:&[u8],out:&mut Vec<u8>) {
    if path.len()>0 && path[0]==b'/' {
        out.extend_from_slice(path);
    } else {
        out.extend_from_slice(base);
        if base.len()>0 && base[base.len()-1]!=b'/' {out.push(b'/');}
        out.extend_from_slice(path);
    }
}
fn check(base:&[u8],path:&[u8]) {
 let native=Path::new(OsStr::from_bytes(base)).join(OsStr::from_bytes(path));
 let mut reference=Vec::new();join_slices_reference(base,path,&mut reference);
 assert_eq!(native.as_os_str().as_bytes(),reference,"base={base:?} path={path:?}");
}
fn main(){
 let mut cases=0u64;
 // Every length0..2 byte pair in each single-coordinate probe, all 256 byte values;
 // separators, NUL and invalid UTF8 are included, plus longer edge strings.
 let alphabet=[0,1,b'/',b'.',b'\\',b':',127,128,255];
 let mut corpus=vec![vec![]];
 for a in alphabet {corpus.push(vec![a]);for b in alphabet {corpus.push(vec![a,b]);}}
 for a in 0..=255 {corpus.push(vec![a]);corpus.push(vec![b'/',a]);corpus.push(vec![a,b'/']);}
 for s in [b"a//b/".as_slice(),b"//",b"///",b"..",b"a/../b",b"",b"C:",b"a\0b",b"a\\b"] {corpus.push(s.to_vec());}
 for b in &corpus {for p in &corpus {check(b,p);cases+=1;}}
 for n in [3,4,7,8,15,16,31,32,63,64,129,1025] {let b:Vec<u8>=(0..n).map(|i|(i*17+29)as u8).collect();for p in &corpus {check(&b,p);check(p,&b);cases+=2;}}
 println!("V178 finite validation: {cases} same-input comparisons; no disagreement");
}
