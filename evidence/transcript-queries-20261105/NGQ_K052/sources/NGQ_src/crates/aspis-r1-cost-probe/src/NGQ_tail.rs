use super::*;
#[derive(Clone,Copy)] struct NGQ_NoDigest;
impl aspis_core::Digest32 for NGQ_NoDigest {
 fn digest(&self,_:&[&[u8]])->[u8;32] {panic!("unexpected digest in tail")}
}
impl<H:aspis_core::Digest32> Transcript<H> {
 fn NGQ_tail(&mut self,reply:Result<([u32;22],[u8;32]),aspis_core::transcript::QuerySampleError>)->Result<[u32;22],crate::verifier::Error> {
        let (q,state)=reply.map_err(|_|crate::verifier::Error::Transcript)?;
        self.state=state;
        { let u=q[0]; crate::trace::value(5,0,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[1]; crate::trace::value(5,1,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[2]; crate::trace::value(5,2,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[3]; crate::trace::value(5,3,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[4]; crate::trace::value(5,4,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[5]; crate::trace::value(5,5,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[6]; crate::trace::value(5,6,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[7]; crate::trace::value(5,7,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[8]; crate::trace::value(5,8,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[9]; crate::trace::value(5,9,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[10]; crate::trace::value(5,10,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[11]; crate::trace::value(5,11,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[12]; crate::trace::value(5,12,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[13]; crate::trace::value(5,13,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[14]; crate::trace::value(5,14,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[15]; crate::trace::value(5,15,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[16]; crate::trace::value(5,16,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[17]; crate::trace::value(5,17,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[18]; crate::trace::value(5,18,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[19]; crate::trace::value(5,19,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[20]; crate::trace::value(5,20,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[21]; crate::trace::value(5,21,E::from_m31(aspis_core::field::M31(u))); }
        Ok(q)
 }
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_tail() {
 let old:[u8;32]=kani::any();let q:[u32;22]=kani::any();let selected:[u8;32]=kani::any();
 let good:bool=kani::any();let tag:u8=kani::any();kani::assume(tag<3);
 let error=match tag {
  0=>aspis_core::transcript::QuerySampleError::BoundNotPowerOfTwo{bound:kani::any()},
  1=>aspis_core::transcript::QuerySampleError::CountExceedsBound{count:kani::any(),bound:kani::any()},
  _=>aspis_core::transcript::QuerySampleError::DrawLimitExhausted{accepted:kani::any(),max_draws:kani::any()},
 };
 let reply=if good {Ok((q,selected))}else{Err(error)};
 let j:usize=kani::any();let i:usize=kani::any();kani::assume(j<32 && i<22);
 let mut t=Transcript{state:old,hash:NGQ_NoDigest};
 let out=t.NGQ_tail(reply);
 let correct=match out {
  Ok(result)=>good && result[i]==q[i] && t.state[j]==selected[j],
  Err(crate::verifier::Error::Transcript)=>!good && t.state[j]==old[j],
  _=>false,
 };
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] { if good { let result=out.unwrap(); assert!(result[i]==(q[i]^1)); } else {assert!(correct);} }
}
