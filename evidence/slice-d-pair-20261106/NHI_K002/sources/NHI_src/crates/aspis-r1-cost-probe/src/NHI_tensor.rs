use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn q(x:[u32;4])->K{K{c0:aspis_core::field::CM31{a:M31(x[0]),b:M31(x[1])},c1:aspis_core::field::CM31{a:M31(x[2]),b:M31(x[3])}}}
fn raw(x:K)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
struct Log{reply:[K;4],left:[[u32;4];4],right:[[u32;4];4],calls:usize}
fn product(x:K,y:K,l:&mut Log)->K{let i=l.calls;l.left[i]=raw(x);l.right[i]=raw(y);l.calls+=1;l.reply[i]}
fn source_window(row:&[K;4],output:&mut[K],j:usize,n:usize,l:&mut Log){
 let x=output[j];
 output[j+0*n]=product(x,row[0],l);
 output[j+1*n]=product(x,row[1],l);
 output[j+2*n]=product(x,row[2],l);
 output[j+3*n]=product(x,row[3],l);
}
fn exercise(g:usize){
 let before:[[u32;4];64]=kani::any();let row_words:[[u32;4];4]=kani::any();let replies:[[u32;4];4]=kani::any();
 let row=core::array::from_fn(|i|q(row_words[i]));let mut output=core::array::from_fn::<K,64,_>(|i|q(before[i]));
 let n:usize=kani::any();kani::assume(n==1||n==4||n==16);let j:usize=kani::any();kani::assume(j<n);
 let frame:usize=kani::any();kani::assume(frame<64);let mut l=Log{reply:core::array::from_fn(|i|q(replies[i])),left:[[0;4];4],right:[[0;4];4],calls:0};
 source_window(&row,&mut output,j,n,&mut l);
 let mut good=if g<16{raw(output[j+(g/4)*n])[g%4]==replies[g/4][g%4]}
 else if g<32{l.left[(g-16)/4][(g-16)%4]==before[j][(g-16)%4]}
 else if g<48{l.right[(g-32)/4][(g-32)%4]==row_words[(g-32)/4][(g-32)%4]}
 else if g<52{if frame!=j&&frame!=j+n&&frame!=j+2*n&&frame!=j+3*n{raw(output[frame])[g-48]==before[frame][g-48]}else{true}}
 else if g==52{l.calls==4}
 else if g==53{j!=j+n&&j+n!=j+2*n&&j+2*n!=j+3*n}
 else if g==54{l.left[3]==before[j]}
 else if g==55{j+3*n<64}
 else if g==56{let mut it=(0..n).rev();let first=it.next();first==Some(n-1)}
 else if g==57{let mut next_n=n;next_n*=4;next_n==4*n}
 else if g==58{let mut ns=[0usize;3];let mut ds=[0usize;3];let mut count=0;let mut width=1;for d in 2..5{ns[count]=width;ds[count]=d;count+=1;width*=4;}count==3&&ns==[1,4,16]&&ds==[2,3,4]&&width==64}
 else{let earlier:usize=kani::any();kani::assume(j<earlier&&earlier<n);j!=earlier&&j+n!=earlier&&j+2*n!=earlier&&j+3*n!=earlier};
 if cfg!(NHI_invert){good=!good;}assert!(good);
}
macro_rules! gate{($name:ident,$n:expr)=>{#[kani::proof]#[kani::unwind(66)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn $name(){exercise($n)}};}
gate!(g00,0);
gate!(g01,1);
gate!(g02,2);
gate!(g03,3);
gate!(g04,4);
gate!(g05,5);
gate!(g06,6);
gate!(g07,7);
gate!(g08,8);
gate!(g09,9);
gate!(g10,10);
gate!(g11,11);
gate!(g12,12);
gate!(g13,13);
gate!(g14,14);
gate!(g15,15);
gate!(g16,16);
gate!(g17,17);
gate!(g18,18);
gate!(g19,19);
gate!(g20,20);
gate!(g21,21);
gate!(g22,22);
gate!(g23,23);
gate!(g24,24);
gate!(g25,25);
gate!(g26,26);
gate!(g27,27);
gate!(g28,28);
gate!(g29,29);
gate!(g30,30);
gate!(g31,31);
gate!(g32,32);
gate!(g33,33);
gate!(g34,34);
gate!(g35,35);
gate!(g36,36);
gate!(g37,37);
gate!(g38,38);
gate!(g39,39);
gate!(g40,40);
gate!(g41,41);
gate!(g42,42);
gate!(g43,43);
gate!(g44,44);
gate!(g45,45);
gate!(g46,46);
gate!(g47,47);
gate!(g48,48);
gate!(g49,49);
gate!(g50,50);
gate!(g51,51);
gate!(g52,52);
gate!(g53,53);
gate!(g54,54);
gate!(g55,55);
gate!(g56,56);
gate!(g57,57);
gate!(g58,58);
gate!(g59,59);
