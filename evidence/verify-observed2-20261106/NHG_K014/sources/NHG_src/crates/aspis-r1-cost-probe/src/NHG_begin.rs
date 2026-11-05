use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)] struct Hash(u64);
impl aspis_core::Digest32 for Hash{fn digest(&self,_:&[&[u8]])->[u8;32]{panic!("all reached calls are packet cuts")}}
fn arbitrary_q()->QM31 {let w:[u32;4]=kani::any();kani::assume(w.iter().all(|&x|x<2147483647));QM31{c0:aspis_core::field::CM31::new(aspis_core::field::M31(w[0]),aspis_core::field::M31(w[1])),c1:aspis_core::field::CM31::new(aspis_core::field::M31(w[2]),aspis_core::field::M31(w[3]))}}
fn any_error()->Error {let tag:u8=kani::any();kani::assume(tag<=10);let row:u8=kani::any();let actual:u8=kani::any();let n:usize=kani::any();match tag {0=>Error::Allocation,1=>Error::RowOrder{expected:row,actual},2=>Error::InvalidRow,3=>Error::Tag{row},4=>Error::Length{row},5=>Error::NonCanonical{row,value:n},6=>Error::Boundary{round:n},7=>Error::Terminal,8=>Error::EqualCirclePoints,9=>Error::TrailingBytes,_=>Error::Public}}

struct BeginLog{calls:usize,fail_at:usize,error:Error,values:[QM31;15],states:[[u8;32];15],nexts:[u8;15],byte:usize,before:[u8;15],cursors:[u8;15],rows:[u8;15],pointers:[*const u8;15],lengths:[usize;15]}
fn NHG_begin_cut(t:&mut SemanticTranscript<Hash>,r:ValidatedRecord<'_>,log:&mut BeginLog)->Result<QM31,Error>{
 let j=log.calls;assert!(j<15);assert!(r.row<=24&&r.framed.len()<=3717);
 log.before[j]=t.state[log.byte];log.cursors[j]=t.next_row;log.rows[j]=r.row;log.pointers[j]=r.framed.as_ptr();log.lengths[j]=r.framed.len();log.calls+=1;
 t.state=log.states[j];t.next_row=log.nexts[j];
 if j==log.fail_at{Err(log.error)}else{Ok(log.values[j])}
}
fn NHG_begin_control(prefix:&Prefix<'_>,transcript:&mut SemanticTranscript<Hash>,log:&mut BeginLog)->Result<Challenges,Error>
{
    let lambda = NHG_begin_cut(transcript,prefix.validated_record(0)?,log)?;
    let chi = NHG_begin_cut(transcript,prefix.validated_record(1)?,log)?;
    let theta = NHG_begin_cut(transcript,prefix.validated_record(2)?,log)?;
    let mut zc = [QM31::ZERO; 10];
    zc[0] = NHG_begin_cut(transcript,prefix.validated_record(3)?,log)?;
    zc[1] = NHG_begin_cut(transcript,prefix.validated_record(4)?,log)?;
    zc[2] = NHG_begin_cut(transcript,prefix.validated_record(5)?,log)?;
    zc[3] = NHG_begin_cut(transcript,prefix.validated_record(6)?,log)?;
    zc[4] = NHG_begin_cut(transcript,prefix.validated_record(7)?,log)?;
    zc[5] = NHG_begin_cut(transcript,prefix.validated_record(8)?,log)?;
    zc[6] = NHG_begin_cut(transcript,prefix.validated_record(9)?,log)?;
    zc[7] = NHG_begin_cut(transcript,prefix.validated_record(10)?,log)?;
    zc[8] = NHG_begin_cut(transcript,prefix.validated_record(11)?,log)?;
    zc[9] = NHG_begin_cut(transcript,prefix.validated_record(12)?,log)?;
    let mu = NHG_begin_cut(transcript,prefix.validated_record(13)?,log)?;
    let eta = NHG_begin_cut(transcript,prefix.validated_record(14)?,log)?;
    Ok(Challenges {
        lambda,
        chi,
        theta,
        zc,
        mu,
        eta,
    })
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_begin_value(){
 let backing=alloc::vec![0u8;17000];let records:[&[u8];27]=core::array::from_fn(|_|{let start:usize=kani::any();let n:usize=kani::any();kani::assume(start<=13000&&n>=5&&n<=3717);&backing[start..start+n]});let root=(&backing[..32]).try_into().unwrap();let prefix=Prefix{c1_root:root,records};
 let values:[QM31;15]=core::array::from_fn(|_|arbitrary_q());let states:[[u8;32];15]=kani::any();let nexts:[u8;15]=kani::any();let fail_at:usize=kani::any();kani::assume(fail_at<=15);let error=any_error();
 let byte:usize=kani::any();kani::assume(byte<32);
 let mut log=BeginLog{byte,calls:0,fail_at,error,values,states,nexts,before:[0;15],cursors:[0;15],rows:[255;15],pointers:[core::ptr::null();15],lengths:[0;15]};
 let hash:u64=kani::any();let initial:[u8;32]=kani::any();let initial_cursor:u8=kani::any();let mut t=SemanticTranscript{state:initial,hash:Hash(hash),next_row:initial_cursor};
 let got=NHG_begin_control(&prefix,&mut t,&mut log);let count=if fail_at<15{fail_at+1}else{15};assert_eq!(log.calls,count);
 let j:usize=kani::any();kani::assume(j<count);let k:usize=kani::any();kani::assume(k<32);
 assert_eq!(log.rows[j]as usize,j);assert_eq!(log.pointers[j],prefix.records[j].as_ptr());assert_eq!(log.lengths[j],prefix.records[j].len());
 assert_eq!(log.before[j],if j==0{initial[byte]}else{states[j-1][byte]});assert_eq!(log.cursors[j],if j==0{initial_cursor}else{nexts[j-1]});
 assert_eq!(t.state[k],states[count-1][k]);assert_eq!(t.next_row,nexts[count-1]);assert_eq!(t.hash.0,hash);
 let correct=match got{Err(e)=>fail_at<15&&e==error,Ok(c)=>fail_at==15&&c.lambda==values[0]&&c.chi==values[1]&&c.theta==values[2]&&c.mu==values[13]&&c.eta==values[14]&&c.zc[j%10]==values[3+j%10]};
 assert!(correct!=cfg!(NHG_invert));
}
