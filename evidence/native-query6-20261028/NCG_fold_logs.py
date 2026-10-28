from pathlib import Path
import difflib
E=Path(__file__).resolve().parent
s=Path('/tmp/NCG_contracts.rs').read_text()
s+='''
static mut NCG_MC:usize=0;static mut NCG_MX:[u32;8]=[0;8];static mut NCG_MY:[u32;8]=[0;8];static mut NCG_MO:[u32;8]=[0;8];
static mut NCG_SC:usize=0;static mut NCG_SX:[[u32;4];16]=[[0;4];16];static mut NCG_SY:[u32;16]=[0;16];static mut NCG_SO:[[u32;4];16]=[[0;4];16];
fn NCG_m31_opaque(x:M31,y:M31)->M31{assert!(x.0<2147483647&&y.0<2147483647);let z:u32=kani::any();kani::assume(z<2147483647);unsafe{let i=NCG_MC;assert!(i<8);NCG_MX[i]=x.0;NCG_MY[i]=y.0;NCG_MO[i]=z;NCG_MC+=1;}M31(z)}
fn NCG_qwords(x:K)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
fn NCG_q(x:[u32;4])->K{use aspis_core::field::CM31;K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn NCG_scalar_opaque(x:K,y:M31)->K{let words=NCG_qwords(x);for w in words{assert!(w<2147483647);}assert!(y.0<2147483647);let z:[u32;4]=kani::any();for w in z{kani::assume(w<2147483647);}unsafe{let i=NCG_SC;assert!(i<16);NCG_SX[i]=words;NCG_SY[i]=y.0;NCG_SO[i]=z;NCG_SC+=1;}NCG_q(z)}
fn NCG_scalar_return(i:usize)->E{unsafe{E::new(NCG_q(NCG_SO[2*i]),NCG_q(NCG_SO[2*i+1]))}}
fn NCG_check_scale(i:usize,x:E,y:u32,k:usize){unsafe{let half=k/4;let word=k%4;assert_eq!(NCG_SX[2*i+half][word],x.to_limbs()[k]);assert_eq!(NCG_SY[2*i],y);assert_eq!(NCG_SY[2*i+1],y);}}
fn NCG_fold_log_case(line:bool,negative:bool){
 let alpha=NCG_e();let values=[NCG_e(),NCG_e(),NCG_e(),NCG_e()];let mut inv:[u32;5]=kani::any();for w in inv{kani::assume(w<2147483647);}let inverse=inv.map(M31);
 let k:usize=kani::any();kani::assume(k<8);
 let out=if line{line_fold_with_inverses(alpha,values,&inverse)}else{circle_fold_with_inverses(alpha,values,&inverse)};
 let [a,b,c,d]=values;let quarter=536870912u32;let half=1073741824u32;
 unsafe{
 assert_eq!(NCG_WCALLS,3);
 let h0=NCG_scalar_return(0);NCG_check_scale(0,a.add(b).add(c).add(d),quarter,k);
 let (h1,h2,h3)=if line{
  assert_eq!(NCG_SC,12);assert_eq!(NCG_MC,4);
  assert_eq!(NCG_MX[0],quarter);assert_eq!(NCG_MY[0],inv[4]);
  assert_eq!(NCG_MX[1],half);assert_eq!(NCG_MY[1],inv[2]);
  assert_eq!(NCG_MX[2],half);assert_eq!(NCG_MY[2],inv[3]);
  assert_eq!(NCG_MX[3],half);assert_eq!(NCG_MY[3],inv[4]);
  NCG_check_scale(1,a.add(b).sub(c).sub(d),NCG_MO[0],k);
  NCG_check_scale(2,a.sub(b),NCG_MO[1],k);NCG_check_scale(3,d.sub(c),NCG_MO[2],k);
  let c0=NCG_scalar_return(2);let c1=NCG_scalar_return(3);
  NCG_check_scale(4,c0.add(c1),half,k);NCG_check_scale(5,c0.sub(c1),NCG_MO[3],k);
  (NCG_scalar_return(4),NCG_scalar_return(1),NCG_scalar_return(5))
 }else{
  assert_eq!(NCG_SC,8);assert_eq!(NCG_MC,4);
  assert_eq!(NCG_MX[0],quarter);assert_eq!(NCG_MY[0],inv[1]);
  assert_eq!(NCG_MX[1],quarter);assert_eq!(NCG_MY[1],inv[0]);
  assert_eq!(NCG_MX[2],quarter);assert_eq!(NCG_MY[2],inv[0]);
  assert_eq!(NCG_MX[3],NCG_MO[2]);assert_eq!(NCG_MY[3],inv[1]);
  NCG_check_scale(1,a.sub(b).sub(c).add(d),NCG_MO[0],k);
  NCG_check_scale(2,a.add(b).sub(c).sub(d),NCG_MO[1],k);
  NCG_check_scale(3,a.sub(b).add(c).sub(d),NCG_MO[3],k);
  (NCG_scalar_return(1),NCG_scalar_return(2),NCG_scalar_return(3))
 };
 assert_eq!(NCG_WX[0][k],alpha.to_limbs()[k]);assert_eq!(NCG_WY[0][k],h3.to_limbs()[k]);
 let t0=h2.add(E::from_limbs(NCG_WO[0]).unwrap());assert_eq!(NCG_WX[1][k],alpha.to_limbs()[k]);assert_eq!(NCG_WY[1][k],t0.to_limbs()[k]);
 let t1=h1.add(E::from_limbs(NCG_WO[1]).unwrap());assert_eq!(NCG_WX[2][k],alpha.to_limbs()[k]);assert_eq!(NCG_WY[2][k],t1.to_limbs()[k]);
 let expected=h0.add(E::from_limbs(NCG_WO[2]).unwrap());
 if negative{assert_ne!(out.to_limbs()[k],expected.to_limbs()[k]);}else{assert_eq!(out.to_limbs()[k],expected.to_limbs()[k]);}
 }
}
'''
attrs='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::stub(aspis_core::field::WideExact::mul,NCG_wide_opaque)]
#[kani::stub(aspis_core::field::QM31::mul_m31,NCG_scalar_opaque)]
#[kani::stub(aspis_core::field::M31::mul,NCG_m31_opaque)]
#[kani::unwind(129)]
'''
for line in [False,True]:
 for neg in [False,True]:s+=attrs+'fn NCG_'+('line' if line else 'circle')+('_negative' if neg else '')+'(){NCG_fold_log_case('+str(line).lower()+','+str(neg).lower()+');}\n'
Path('/tmp/NCG_fold_logs.rs').write_text(s)
(E/'NCG_fold_logs.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NCG_native.rs')))
