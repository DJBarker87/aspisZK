from pathlib import Path
E=Path(__file__).resolve().parent
p=E/'NIG_stages.patch';s=p.read_text();i=s.index('--- /dev/null\n+++ b/crates/aspis-r1-cost-probe/src/NIG_stages.rs');head=s[:i];h=''.join(l[1:]for l in s[i:].splitlines(True)if l.startswith('+')and not l.startswith('+++'))
h+='''
fn anye()->E{let v:[u32;8]=kani::any();for x in v{kani::assume(x<0x7fffffff);}E::from_limbs(v).unwrap()}
struct Low{a:E,b:E,product:E,scale_a:E,scale_b:M31,scaled:E,base_a:M31,base_b:M31,tags:[u8;3],count:usize}
fn emul(a:E,b:E,l:&mut Low)->E{l.a=a;l.b=b;l.tags[l.count]=0;l.count+=1;l.product}
fn square(a:M31,b:M31,l:&mut Low)->M31{l.base_a=a;l.base_b=b;l.tags[l.count]=1;l.count+=1;M31(134217728)}
fn scale(a:E,b:M31,l:&mut Low)->E{l.scale_a=a;l.scale_b=b;l.tags[l.count]=2;l.count+=1;l.scaled}
fn low_cut(ap0:&[E;4],ap1:&[E;4],s:usize,cells:&mut [E;16],l:&mut Low){
 let product=emul(ap0[PERM[s%4]],ap1[PERM[s/4]],l);
 let base=square(QUARTER,QUARTER,l);
 cells[s]=scale(product,base,l);
}
fn low_check(g:usize){
 let ap0=core::array::from_fn(|_|anye());let ap1=core::array::from_fn(|_|anye());
 let before=core::array::from_fn(|_|anye());let mut cells=before;
 let s:usize=kani::any();kani::assume(s<16);let k:usize=kani::any();kani::assume(k<16);
 let limb:usize=kani::any();kani::assume(limb<8);
 let mut l=Low{a:E::ZERO,b:E::ZERO,product:anye(),scale_a:E::ZERO,scale_b:M31(0),scaled:anye(),base_a:M31(0),base_b:M31(0),tags:[99;3],count:0};
 low_cut(&ap0,&ap1,s,&mut cells,&mut l);
 if cfg!(NIG_corrupt){match g{0=>l.a=E::ZERO,1=>l.b=E::ZERO,2=>l.tags[0]=99,3=>l.base_b=M31(0),4=>l.scale_a=E::ZERO,_=>cells[k]=E::ZERO}}
 let good=match g{0=>l.a.to_limbs()[limb]==ap0[PERM[s%4]].to_limbs()[limb],1=>l.b.to_limbs()[limb]==ap1[PERM[s/4]].to_limbs()[limb],2=>l.count==3&&l.tags==[0,1,2],3=>l.base_a==QUARTER&&l.base_b==QUARTER&&l.scale_b==M31(134217728),4=>l.scale_a.to_limbs()[limb]==l.product.to_limbs()[limb],_=>cells[k].to_limbs()[limb]==if k==s{l.scaled}else{before[k]}.to_limbs()[limb]};assert!(good);
}
macro_rules! lowgate{($name:ident,$g:expr)=>{#[kani::proof]#[kani::unwind(194)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn $name(){low_check($g)}};}
lowgate!(low_lhs,0);lowgate!(low_rhs,1);lowgate!(low_order,2);lowgate!(low_scalar,3);lowgate!(low_scale,4);lowgate!(low_frame,5);
'''
p.write_text(head+'--- /dev/null\n+++ b/crates/aspis-r1-cost-probe/src/NIG_stages.rs\n@@ -0,0 +1,'+str(len(h.splitlines()))+' @@\n'+''.join('+'+l for l in h.splitlines(True)))
