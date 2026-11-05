from pathlib import Path
E=Path(__file__).resolve().parent;p=E/'NIG_stages.patch';s=p.read_text();i=s.index('--- /dev/null\n+++ b/crates/aspis-r1-cost-probe/src/NIG_stages.rs');head=s[:i];h=''.join(l[1:]for l in s[i:].splitlines(True)if l.startswith('+')and not l.startswith('+++'))
h+='''
struct Final{mul_a:E,mul_b:E,product:E,add_a:E,add_b:E,reply:E,count:usize,tags:[u8;2]}
fn final_mul(a:E,b:E,l:&mut Final)->E{l.mul_a=a;l.mul_b=b;l.tags[l.count]=0;l.count+=1;l.product}
fn final_add(a:E,b:E,l:&mut Final)->E{l.add_a=a;l.add_b=b;l.tags[l.count]=1;l.count+=1;l.reply}
fn final_cut(parts:&[E;7],powers:&[E;7],kind:usize,sum:&mut E,l:&mut Final){
 let product=final_mul(powers[kind],parts[kind],l);*sum=final_add(*sum,product,l);
}
fn final_check(g:usize){
 let parts=core::array::from_fn(|_|anye());let powers=core::array::from_fn(|_|anye());
 let before=anye();let mut sum=before;let kind:usize=kani::any();kani::assume(kind<7);
 let limb:usize=kani::any();kani::assume(limb<8);
 let mut l=Final{mul_a:E::ZERO,mul_b:E::ZERO,product:anye(),add_a:E::ZERO,add_b:E::ZERO,reply:anye(),count:0,tags:[99;2]};
 final_cut(&parts,&powers,kind,&mut sum,&mut l);
 if cfg!(NIG_corrupt){match g{0=>l.mul_a=E::ZERO,1=>l.mul_b=E::ZERO,2=>l.add_a=E::ZERO,3=>l.add_b=E::ZERO,4=>l.tags[0]=99,_=>sum=E::ZERO}}
 let good=match g{0=>l.mul_a.to_limbs()[limb]==powers[kind].to_limbs()[limb],1=>l.mul_b.to_limbs()[limb]==parts[kind].to_limbs()[limb],2=>l.add_a.to_limbs()[limb]==before.to_limbs()[limb],3=>l.add_b.to_limbs()[limb]==l.product.to_limbs()[limb],4=>l.count==2&&l.tags==[0,1],_=>sum.to_limbs()[limb]==l.reply.to_limbs()[limb]};assert!(good);
}
macro_rules! finalgate{($name:ident,$g:expr)=>{#[kani::proof]#[kani::unwind(130)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn $name(){final_check($g)}};}
finalgate!(final_power,0);finalgate!(final_part,1);finalgate!(final_sum,2);finalgate!(final_product,3);finalgate!(final_order,4);finalgate!(final_result,5);
'''
p.write_text(head+'--- /dev/null\n+++ b/crates/aspis-r1-cost-probe/src/NIG_stages.rs\n@@ -0,0 +1,'+str(len(h.splitlines()))+' @@\n'+''.join('+'+l for l in h.splitlines(True)))
