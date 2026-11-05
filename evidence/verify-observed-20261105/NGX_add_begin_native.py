from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent;p=E/'NGX_native.rs.txt';s=p.read_text();assert 'fn begin_control'not in s
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/r1_wire.rs'],text=True)
start=frozen.index('pub fn begin<H: Digest32>(');a=frozen.index('{',start);d=1;i=a+1
while d:d+=(frozen[i]=='{')-(frozen[i]=='}');i+=1
original=frozen[start:i];cut,count=re.subn(r'transcript.semantic_validated\(prefix.validated_record\((\d+)\)\?\)',r'begin_semantic_cut(transcript,prefix.validated_record(\1)?,log)',frozen[a:i]);assert count==15
s+='''
fn arbitrary_q()->QM31 {let w:[u32;4]=kani::any();kani::assume(w.iter().all(|&x|x<2147483647));QM31{c0:aspis_core::field::CM31::new(aspis_core::field::M31(w[0]),aspis_core::field::M31(w[1])),c1:aspis_core::field::CM31::new(aspis_core::field::M31(w[2]),aspis_core::field::M31(w[3]))}}
struct BeginLog {calls:usize,fail_at:usize,error:Error,values:[QM31;15],states:[[u8;32];15],rows:[u8;15],pointers:[*const u8;15],lengths:[usize;15]}
fn begin_semantic_cut(t:&mut SemanticTranscript<Hash>,record:ValidatedRecord<'_>,log:&mut BeginLog)->Result<QM31,Error> {
 let j=log.calls;assert!(j<15);assert!(record.row<=24&&record.framed.len()<=3717);log.calls+=1;log.rows[j]=record.row;log.pointers[j]=record.framed.as_ptr();log.lengths[j]=record.framed.len();
 t.state=log.states[j];t.next_row=record.row+1;
 if j==log.fail_at{Err(log.error)}else{Ok(log.values[j])}
}
fn begin_control(prefix:&Prefix<'_>,transcript:&mut SemanticTranscript<Hash>,log:&mut BeginLog)->Result<Challenges,Error>
'''+cut+'''
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn begin_value() {
 let backing=alloc::vec![0u8;17000];let records:[&[u8];27]=core::array::from_fn(|_|{let start:usize=kani::any();let n:usize=kani::any();kani::assume(start<=13000&&n>=5&&n<=3717);&backing[start..start+n]});let root=(&backing[..32]).try_into().unwrap();let prefix=Prefix{c1_root:root,records};
 let values:[QM31;15]=core::array::from_fn(|_|arbitrary_q());let states:[[u8;32];15]=kani::any();let fail_at:usize=kani::any();kani::assume(fail_at<=15);let error=any_error();
 let mut log=BeginLog{calls:0,fail_at,error,values,states,rows:[255;15],pointers:[core::ptr::null();15],lengths:[0;15]};let hash:u64=kani::any();let mut t=SemanticTranscript{state:kani::any(),hash:Hash(hash),next_row:kani::any()};let got=begin_control(&prefix,&mut t,&mut log);
 let count=if fail_at<15{fail_at+1}else{15};assert_eq!(log.calls,count);let j:usize=kani::any();kani::assume(j<count);assert_eq!(log.rows[j]as usize,j);assert_eq!(log.pointers[j],prefix.records[j].as_ptr());assert_eq!(log.lengths[j],prefix.records[j].len());let k:usize=kani::any();kani::assume(k<32);assert_eq!(t.state[k],states[count-1][k]);assert_eq!(t.next_row,count as u8);assert_eq!(t.hash.0,hash);
 let correct=match got {Err(e)=>fail_at<15&&e==error,Ok(c)=>fail_at==15&&c.lambda==values[0]&&c.chi==values[1]&&c.theta==values[2]&&c.mu==values[13]&&c.eta==values[14]&&c.zc[j%10]==values[3+j%10]};assert!(correct!=cfg!(NGX_invert));
}
'''
p.write_text(s);(E/'NGX_BEGIN_CUT.json').write_text(json.dumps(dict(original_body=original,cut_body=cut,callee_substitutions=count,credit='native control support only; actual semantic state/effects producer association still required'),indent=1))
m=json.loads((E/'NGX_OVERLAY.json').read_text());(E/'NGX_SOURCE_PINS.json').write_text(json.dumps({k:hashlib.sha256((E/v).read_bytes()).hexdigest()for k,v in m.items()},indent=1))
