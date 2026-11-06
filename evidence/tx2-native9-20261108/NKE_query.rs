use super::*;
struct Log<'a,const PART:usize>{
 proof:&'a[u8],p:&'a Prepared,g:&'a[E;29],geometry:&'a QueryGeometry,
 weights:&'a[[u32;4];64],wp:*const K,wc:usize,rhs:E,power:K,next:usize,
 rows:&'a[[u64;4];64],rp:*const [u64;4],rc:usize,terms:usize,
 reply:Option<Result<(Accumulator,BatchedWeights),Error>>,calls:usize,
}
impl<const PART:usize> Log<'_,PART>{
 fn query(&mut self,proof:&[u8],p:&Prepared,a:Accumulator,g:&[E;29],_obs:Observer,
  geometry:&QueryGeometry,pending:BatchedWeights,end:usize)->Result<(Accumulator,BatchedWeights),Error>{
  self.calls+=1;assert_eq!(end,22);
  if PART==0 || PART==4{
   assert_eq!(proof.as_ptr(),self.proof.as_ptr());assert_eq!(proof.len(),self.proof.len());if PART==0{let b=kani::any::<u16>() as usize;kani::assume(b<57607);assert_eq!(proof[b],self.proof[b]^(if cfg!(NKE_invert){1}else{0}));}else{assert_eq!(proof.len(),57607^(if cfg!(NKE_invert){1}else{0}));}
   assert_eq!(p as *const Prepared,self.p as *const Prepared);assert!(p.variant==Variant::S2);assert_eq!(p.roots,self.p.roots);assert_eq!(p.gamma,self.p.gamma);assert_eq!(p.kappa,self.p.kappa);assert_eq!(p.alpha,self.p.alpha);assert_eq!(p.rho,self.p.rho);assert_eq!(p.queries,self.p.queries);assert_eq!(p.semantic_alpha,self.p.semantic_alpha);assert_eq!(p.claim,self.p.claim);assert_eq!(p.state,self.p.state);assert_eq!(p.z[0].x,self.p.z[0].x);assert_eq!(p.z[0].y,self.p.z[0].y);assert_eq!(p.z[1].x,self.p.z[1].x);assert_eq!(p.z[1].y,self.p.z[1].y);
   assert_eq!(g as *const [E;29],self.g as *const [E;29]);let i=(kani::any::<u8>()&31) as usize;kani::assume(i<29);assert_eq!(g[i],self.g[i]);
  }
  if PART==1{
   assert_eq!(a.weights.as_ptr(),self.wp);assert_eq!(a.weights.capacity(),self.wc);assert_eq!(a.weights.len(),64);let i=(kani::any::<u8>()&63) as usize;assert_eq!(a.weights[i].c0.a.0,self.weights[i][0]^(if cfg!(NKE_invert){1}else{0}));assert_eq!(a.weights[i].c0.b.0,self.weights[i][1]);assert_eq!(a.weights[i].c1.a.0,self.weights[i][2]);assert_eq!(a.weights[i].c1.b.0,self.weights[i][3]);assert_eq!(a.rhs,self.rhs);assert_eq!(a.power,self.power);assert_eq!(a.next,self.next);
  }
  if PART==2{
   assert_eq!(geometry as *const QueryGeometry,self.geometry as *const QueryGeometry);assert_eq!(geometry.start,self.geometry.start);assert_eq!(geometry.inverses.as_ptr(),self.geometry.inverses.as_ptr());assert_eq!(geometry.inverses.len(),12);assert_eq!(geometry.inverses.capacity(),self.geometry.inverses.capacity());assert_eq!(geometry.line_z.as_ptr(),self.geometry.line_z.as_ptr());assert_eq!(geometry.line_z.len(),12);assert_eq!(geometry.line_z.capacity(),self.geometry.line_z.capacity());let i=(kani::any::<u8>()&15) as usize;kani::assume(i<12);let j=(kani::any::<u8>()&7) as usize;kani::assume(j<5);assert_eq!(geometry.inverses[i][j].0,self.geometry.inverses[i][j].0);assert_eq!(geometry.line_z[i].0,self.geometry.line_z[i].0);
   assert_eq!(pending.raw.as_ptr(),self.rp);assert_eq!(pending.raw.capacity(),self.rc);assert_eq!(pending.raw.len(),64);assert_eq!(pending.terms,self.terms);let i=(kani::any::<u8>()&63) as usize;let expected=self.rows[i];assert_eq!(pending.raw[i][0],expected[0]^(if cfg!(NKE_invert){1}else{0}));assert_eq!(pending.raw[i][1],expected[1]);assert_eq!(pending.raw[i][2],expected[2]);assert_eq!(pending.raw[i][3],expected[3]);
  }
  self.reply.take().unwrap()
 }
}
// Frozen candidate::tx2_common query boundary. None is the deployed constant;
// no observer/function-pointer value is compared or otherwise inspected.
fn stage<const PART:usize>(proof:&[u8],p:&Prepared,a:Accumulator,g:&[E;29],
 geometry:&QueryGeometry,pending:BatchedWeights,log:&mut Log<PART>)->Result<(Accumulator,BatchedWeights),Error>{
 let (a,pending)=log.query(proof,p,a,g,None,geometry,pending,22)?;Ok((a,pending))
}
fn window<const PART:usize>(){
 let proof:[u8;57607]=kani::any();let p=prepared();let gw:[[u32;8];29]=kani::any();let g=gw.map(|w|E::new(k([w[0],w[1],w[2],w[3]]),k([w[4],w[5],w[6],w[7]])));
 let weights:[[u32;4];64]=kani::any();let rows:[[u64;4];64]=kani::any();let postw:[[u32;4];64]=kani::any();let postr:[[u64;4];64]=kani::any();let mut w=alloc::vec::Vec::with_capacity(64);let mut r=alloc::vec::Vec::with_capacity(64);let mut ow=alloc::vec::Vec::with_capacity(64);let mut or=alloc::vec::Vec::with_capacity(64);
 for v in weights{w.push(k(v));}for v in rows{r.push(v);}for v in postw{ow.push(k(v));}for v in postr{or.push(v);}
 let inv:[[u32;5];12]=kani::any();let line:[u32;12]=kani::any();let mut inverses=alloc::vec::Vec::with_capacity(12);let mut line_z=alloc::vec::Vec::with_capacity(12);for v in inv{inverses.push(v.map(M31));}for v in line{line_z.push(M31(v));}let geometry=QueryGeometry{start:kani::any(),inverses,line_z};
 let rhs=any_e();let power=k(kani::any());let next:usize=kani::any();let terms:usize=kani::any();let good:bool=kani::any();let err=error(kani::any());let reply=if good{Ok((Accumulator{weights:ow,rhs:any_e(),power:k(kani::any()),next:kani::any()},BatchedWeights{raw:or,terms:kani::any()}))}else{Err(err)};
 let mut log=Log::<PART>{proof:&proof,p:&p,g:&g,geometry:&geometry,weights:&weights,wp:w.as_ptr(),wc:w.capacity(),rhs,power,next,rows:&rows,rp:r.as_ptr(),rc:r.capacity(),terms,reply:Some(reply),calls:0};
 let out=stage(&proof,&p,Accumulator{weights:w,rhs,power,next},&g,&geometry,BatchedWeights{raw:r,terms},&mut log);assert_eq!(log.calls,1);assert!(log.reply.is_none());assert_eq!(out.is_ok(),good);if let Err(e)=out{assert_eq!(e,err);}
}
#[kani::proof]
#[kani::unwind(930)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn borrowed(){window::<0>();}
#[kani::proof]
#[kani::unwind(930)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn accumulator(){window::<1>();}
#[kani::proof]
#[kani::unwind(930)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn geometry_pending(){window::<2>();}
#[kani::proof]
#[kani::unwind(930)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn borrowed_rename_control(){window::<0>();}

#[kani::proof]
#[kani::unwind(930)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn accumulator_rename_control(){window::<1>();}

#[kani::proof]
#[kani::unwind(930)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn borrowed_handles_prepared_powers(){window::<4>();}
