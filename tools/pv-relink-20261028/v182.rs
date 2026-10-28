fn push_bytes_reference(s:&mut Vec<u8>,t:&[u8]) {s.extend_from_slice(t)}
fn check(s:&str,t:&str){
 let mut native=s.to_owned();let mut reference=s.as_bytes().to_vec();
 native.push_str(t);push_bytes_reference(&mut reference,t.as_bytes());
 assert_eq!(native.as_bytes(),reference,"s={s:?} t={t:?}");
 assert_eq!(String::from_utf8(reference).unwrap(),native);
}
fn main(){let mut cases=0u64;
 let corpus=["","a","/","\0","é","🦀","..","a//b/","\u{7f}","\u{80}","\u{7ff}","\u{800}","\u{ffff}","\u{10000}","\u{10ffff}"];
 for s in corpus {for t in corpus{check(s,t);cases+=1;}}
 // Every Unicode scalar in each position, including multi-byte boundaries.
 for n in 0..=0x10ffff {if let Some(c)=char::from_u32(n){let s=c.to_string();check(&s,"a");check("é",&s);check(&s,&s);cases+=3;}}
 // All valid UTF8 2-byte initial values and every ASCII one-byte suffix.
 for a in 0..=255u8 {for b in 0..=255u8{if let Ok(s)=std::str::from_utf8(&[a,b]){for t in 0..=127u8{check(s,std::str::from_utf8(&[t]).unwrap());cases+=1;}}}}
 for n in [8,16,31,32,63,64,129,1025]{let s="é\0/🦀".repeat(n);check(&s,&s);cases+=1;}
 println!("V182 finite validation: {cases} same-input comparisons; no disagreement");}
