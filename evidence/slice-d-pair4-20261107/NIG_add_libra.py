from pathlib import Path
E=Path(__file__).resolve().parent;p=E/'NIG_stages.patch';s=p.read_text();i=s.index('--- /dev/null\n+++ b/crates/aspis-r1-cost-probe/src/NIG_stages.rs');head=s[:i];h=''.join(l[1:]for l in s[i:].splitlines(True)if l.startswith('+')and not l.startswith('+++'))
h+='''
struct LibraLog{ptr:*const u8,len:usize,index:usize,coefficient:E,mul_a:E,mul_b:E,product:E,add_a:E,add_b:E,reply:E,count:usize,tags:[u8;3]}
fn libra_field(f:&[u8],j:usize,l:&mut LibraLog)->E{l.ptr=f.as_ptr();l.len=f.len();l.index=j;l.tags[l.count]=0;l.count+=1;l.coefficient}
fn libra_mul(a:E,b:E,l:&mut LibraLog)->E{l.mul_a=a;l.mul_b=b;l.tags[l.count]=1;l.count+=1;l.product}
fn libra_add(a:E,b:E,l:&mut LibraLog)->E{l.add_a=a;l.add_b=b;l.tags[l.count]=2;l.count+=1;l.reply}
fn libra_cut(f:&[u8],libra:&[E;4],j:usize,parts:&mut [E;7],l:&mut LibraLog){
 let old=parts[4];let coefficient=libra_field(f,j,l);let weight=libra[j];let product=libra_mul(coefficient,weight,l);parts[4]=libra_add(old,product,l);
}
fn libra_check(g:usize){
 let f:[u8;2048]=kani::any();let libra=core::array::from_fn(|_|anye());let before=core::array::from_fn(|_|anye());let mut parts=before;
 let j:usize=kani::any();kani::assume(j<4);let k:usize=kani::any();kani::assume(k<7);let limb:usize=kani::any();kani::assume(limb<8);
 let mut l=LibraLog{ptr:core::ptr::null(),len:0,index:99,coefficient:anye(),mul_a:E::ZERO,mul_b:E::ZERO,product:anye(),add_a:E::ZERO,add_b:E::ZERO,reply:anye(),count:0,tags:[99;3]};
 libra_cut(&f,&libra,j,&mut parts,&mut l);
 if cfg!(NIG_corrupt){match g{0=>l.index=99,1=>l.mul_a=E::ZERO,2=>l.mul_b=E::ZERO,3=>l.add_a=E::ZERO,4=>l.add_b=E::ZERO,_=>parts[k]=E::ZERO}}
 let good=match g{0=>l.ptr==f.as_ptr()&&l.len==2048&&l.index==j&&l.count==3&&l.tags==[0,1,2],1=>l.mul_a.to_limbs()[limb]==l.coefficient.to_limbs()[limb],2=>l.mul_b.to_limbs()[limb]==libra[j].to_limbs()[limb],3=>l.add_a.to_limbs()[limb]==before[4].to_limbs()[limb],4=>l.add_b.to_limbs()[limb]==l.product.to_limbs()[limb],_=>parts[k].to_limbs()[limb]==if k==4{l.reply}else{before[k]}.to_limbs()[limb]};assert!(good);
}
macro_rules! libragate{($name:ident,$g:expr)=>{#[kani::proof]#[kani::unwind(2050)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn $name(){libra_check($g)}};}
libragate!(libra_field_args,0);libragate!(libra_coefficient,1);libragate!(libra_weight,2);libragate!(libra_old,3);libragate!(libra_product,4);libragate!(libra_frame,5);
'''
p.write_text(head+'--- /dev/null\n+++ b/crates/aspis-r1-cost-probe/src/NIG_stages.rs\n@@ -0,0 +1,'+str(len(h.splitlines()))+' @@\n'+''.join('+'+l for l in h.splitlines(True)))
