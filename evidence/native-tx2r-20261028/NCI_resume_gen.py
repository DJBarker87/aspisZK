from NCI_extend import extend,attrs
h='''
#[cfg(kani)] mod NCI_resume {
use super::*;
use core::cell::Cell;
#[derive(Clone,Copy)] struct Request<'a>{calls:&'a Cell<usize>,stop:usize,proof:&'a[u8],public:&'a[u8],saved:&'a[u8]}
impl Digest32 for Request<'_>{fn digest(&self,parts:&[&[u8]])->[u8;32]{
 let call=self.calls.get();assert!(call<3);
 if call==0{assert!(parts.len()==1);assert!(parts[0].as_ptr()==self.proof.as_ptr()&&parts[0].len()==57607);}
 if call==1{assert!(parts.len()==1);assert!(parts[0].as_ptr()==self.public.as_ptr()&&parts[0].len()==1880);}
 if call==2{assert!(parts.len()==2);assert!(parts[0]==b"UNPROVED:R1:checkpoint");assert!(parts[1].as_ptr()==self.saved.as_ptr()&&parts[1].len()==1736);}
 self.calls.set(call+1);if call==self.stop{[1u8;32]}else{[0u8;32]}
}}
'''
for stop in range(3):
 for wrong in [False,True]:
  h+=attrs+f'''fn stop{stop}_{'wrong' if wrong else 'ok'}(){{
let mut saved=[0u8;1768];saved[..8].copy_from_slice(b"R1P2CKP2");saved[8]=2;saved[10]=1;
let next:u8=kani::any();kani::assume(next<=22);saved[9]=next;
let proof=[0u8;57607];let public=[0u8;1880];let count=Cell::new(0usize);
let hash=Request{{calls:&count,stop:{stop},proof:&proof,public:&public,saved:&saved}};
let out=resume(&saved,&proof,&public,Variant::S2,hash);
assert!(matches!(out,Err(Error::Checkpoint)));assert!(count.get(){'!=' if wrong else '=='}{stop+1});
}}\n'''
for wrong in [False,True]:
 h+=attrs+f'''fn header_{'wrong' if wrong else 'ok'}(){{
let mut saved=[0u8;1768];saved[..8].copy_from_slice(b"R1P2CKP2");saved[8]=2;saved[10]=1;
let fault:u8=kani::any();kani::assume(fault<6);
match fault{{0=>saved[0]=0,1=>saved[8]=3,2=>saved[9]=23,3=>saved[10]=0,4=>saved[11]=1,_=>saved[15]=1}}
let proof=[0u8;57607];let public=[0u8;1880];let count=Cell::new(0usize);
let hash=Request{{calls:&count,stop:0,proof:&proof,public:&public,saved:&saved}};
let out=resume(&saved,&proof,&public,Variant::S2,hash);
assert!(matches!(out,Err(Error::Checkpoint)));assert!(count.get(){'!=' if wrong else '=='}0);
}}\n'''
h+='}\n'
extend('NCI_resume.patch',h)
