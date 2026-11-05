from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent;p=E/'NGX_native.rs.txt';s=p.read_text();assert 'fn semantic_control' not in s
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/r1_wire.rs'],text=True)
start=frozen.index('pub(crate) fn semantic_validated(');a=frozen.index('{',start);depth=1;i=a+1
while depth:depth+=(frozen[i]=='{')-(frozen[i]=='}');i+=1
original=frozen[start:i];body=frozen[a:i];cut=body.replace('self.sample_block_validated(row, record.framed())?','semantic_block_cut(t, row, record.framed(), log)?').replace('qm31_sample(','semantic_qm_cut(').replace('?,\n        ))','?, log))')
s+='''
struct SemanticLog {calls:usize,sampler:usize,ptr:*const u8,length:usize,row:u8,block:[u8;32],final_state:[u8;32],q:QM31,seen:[u8;32]}
fn semantic_block_cut(t:&mut SemanticTranscript<Hash>,row:u8,frame:&[u8],log:&mut SemanticLog)->Result<[u8;32],Error> {
 assert!(row<=24&&frame.len()<=3717);log.calls+=1;log.row=row;log.ptr=frame.as_ptr();log.length=frame.len();
 if row!=t.next_row {return Err(Error::RowOrder{expected:t.next_row,actual:row});}
 t.state=log.final_state;t.next_row+=1;Ok(log.block)
}
fn semantic_qm_cut(block:&[u8;32],log:&mut SemanticLog)->QM31 {log.sampler+=1;log.seen=*block;log.q}
fn semantic_control(t:&mut SemanticTranscript<Hash>,record:ValidatedRecord<'_>,log:&mut SemanticLog)->Result<QM31,Error>
'''+cut+'''
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn semantic_value() {
 let row:u8=kani::any();let next:u8=kani::any();let length:usize=kani::any();kani::assume(length>=5&&length<=3717);
 let backing=alloc::vec![0u8;length];let state:[u8;32]=kani::any();let final_state:[u8;32]=kani::any();let block:[u8;32]=kani::any();let hash:u64=kani::any();
 let a:u32=kani::any();let b:u32=kani::any();let c:u32=kani::any();let d:u32=kani::any();kani::assume(a<2147483647&&b<2147483647&&c<2147483647&&d<2147483647);
 let q=QM31{c0:aspis_core::field::CM31::new(aspis_core::field::M31(a),aspis_core::field::M31(b)),c1:aspis_core::field::CM31::new(aspis_core::field::M31(c),aspis_core::field::M31(d))};
 let mut log=SemanticLog{calls:0,sampler:0,ptr:core::ptr::null(),length:0,row:0,block,final_state,q,seen:[0;32]};let mut t=SemanticTranscript{state,hash:Hash(hash),next_row:next};
 let got=semantic_control(&mut t,ValidatedRecord{row,framed:&backing},&mut log);let k:usize=kani::any();kani::assume(k<32);
 let correct=if row>24 {matches!(got,Err(Error::InvalidRow))&&log.calls==0&&log.sampler==0&&t.state[k]==state[k]&&t.next_row==next}
 else if row!=next {matches!(got,Err(Error::RowOrder{expected,actual})if expected==next&&actual==row)&&log.calls==1&&log.sampler==0&&t.state[k]==state[k]&&t.next_row==next}
 else {got==Ok(q)&&log.calls==1&&log.sampler==1&&log.seen[k]==block[k]&&t.state[k]==final_state[k]&&t.next_row==next+1};
 assert!(correct!=cfg!(NGX_invert));assert_eq!(t.hash.0,hash);if row<=24 {assert_eq!(log.ptr,backing.as_ptr());assert_eq!(log.length,length);assert_eq!(log.row,row);}
}
'''
p.write_text(s);(E/'NGX_SEMANTIC_CUT.json').write_text(json.dumps(dict(original_body=original,cut_body=cut,substitutions=['sample_block_validated -> exact-domain local-record packet cut','qm31_sample -> same-block local-record sampler packet cut']),indent=1))
