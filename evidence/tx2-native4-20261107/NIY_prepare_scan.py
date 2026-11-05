from pathlib import Path
import json,hashlib,subprocess,re
E=Path(__file__).resolve().parent;x=json.loads((E/'NIY_NATIVE_INPUTS.json').read_text());p='crates/aspis-r1-cost-probe/src/candidate.rs';frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
a=frozen.index('fn canonical_scan');b=frozen.index('    for i in 0..22',a);prefix=frozen[a:b]
expected='''fn canonical_scan(proof: &[u8]) -> Result<(), Error> {
    compact::check_values(&proof[compact::OFF_Y1..compact::OFF_INACTIVE])?;
    echeck(&proof[compact::OFF_INACTIVE..compact::OFF_INACTIVE + 32], false)?;
    echeck(&proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT], false)?;
    echeck(&proof[compact::OFF_ROUND1..compact::OFF_OPENINGS], false)?;
'''
assert re.sub(r'\s+','',prefix)==re.sub(r'\s+','',expected)
s='''use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
fn error()->Error{match kani::any::<u8>()&7{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
struct Log<'a>{proof:&'a[u8],ok:[bool;4],errors:[Error;4],calls:usize}
impl Log<'_>{fn enter(&mut self,bytes:&[u8],mode:Option<bool>)->Result<(),Error>{
 let c=self.calls;assert!(c<4);
 let (start,end)=match c{0=>(compact::OFF_Y1,compact::OFF_INACTIVE),1=>(compact::OFF_INACTIVE,compact::OFF_INACTIVE+32),2=>(compact::OFF_ROUND0,compact::OFF_FOLDED_ROOT),_=>(compact::OFF_ROUND1,compact::OFF_OPENINGS)};
 let ptr=bytes.as_ptr() as usize^(if cfg!(NIY_invert){1}else{0});assert_eq!(ptr,self.proof[start..end].as_ptr() as usize);assert_eq!(bytes.len(),end-start);assert_eq!(mode,if c==0{None}else{Some(false)});
 self.calls+=1;if self.ok[c]{Ok(())}else{Err(self.errors[c])}
}}
fn prefix(proof:&[u8],log:&mut Log<'_>,tail:Result<(),Error>)->Result<(),Error>{
 log.enter(&proof[compact::OFF_Y1..compact::OFF_INACTIVE],None)?;
 log.enter(&proof[compact::OFF_INACTIVE..compact::OFF_INACTIVE+32],Some(false))?;
 log.enter(&proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],Some(false))?;
 log.enter(&proof[compact::OFF_ROUND1..compact::OFF_OPENINGS],Some(false))?;
 tail
}
fn prefix_check(){let proof:[u8;57607]=kani::any();let ok:[bool;4]=kani::any();let errors=[error(),error(),error(),error()];let tail=if kani::any(){Ok(())}else{Err(error())};
 let mut log=Log{proof:&proof,ok,errors,calls:0};let result=prefix(&proof,&mut log,tail);
 assert_eq!(log.calls,if !ok[0]{1}else if !ok[1]{2}else if !ok[2]{3}else{4});
 let expected=if !ok[0]{Err(errors[0])}else if !ok[1]{Err(errors[1])}else if !ok[2]{Err(errors[2])}else if !ok[3]{Err(errors[3])}else{tail};assert_eq!(result,expected);
}
fn m31_step_check(){let q:[u8;832]=kani::any();let s:usize=kani::any();kani::assume(s<4);let l:usize=kani::any();kani::assume(l<=26);let mut range=l..26;let next=range.next();
 match next{None=>{assert_eq!(l,26);assert_eq!(range.len(),0);},Some(current)=>{assert_eq!(current,l);assert_eq!(range.len(),25-l);let at=s*120+current*4;let actual=M31::from_le_bytes(q[at..at+4].try_into().unwrap()).ok_or(Error::Parse).map(|_|());let expected=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]])<0x7fffffff;assert_eq!(actual.is_ok(),expected^cfg!(NIY_invert));if let Err(error)=actual{assert_eq!(error,Error::Parse);}}}
}
fn opening_check(){let proof:[u8;57607]=kani::any();let i:usize=kani::any();kani::assume(i<22);let j:usize=kani::any();kani::assume(j<832);let q=opening(&proof,i);let start=compact::OFF_OPENINGS+i*832;assert_eq!(compact::OFF_OPENINGS,10055);assert_eq!(q.len(),832);assert_eq!(q.as_ptr(),proof[start..start+832].as_ptr());assert_eq!(q[j],proof[start+j]^(if cfg!(NIY_invert){1}else{0}));}
'''
for name,call in [('scan_prefix','prefix_check();'),('scan_m31_step','m31_step_check();'),('scan_opening','opening_check();')]:
 for suffix in ['', '_renamed']:
  s+='#[kani::proof]\n#[kani::unwind(36)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]\nfn '+name+suffix+'(){'+call+'}\n'
x[p]+='\n#[cfg(kani)]\n#[path="NIY_scan_native.rs"]\nmod NIY_scan_native;\n';n='crates/aspis-r1-cost-probe/src/NIY_scan_native.rs';x[n]=s
(E/'NIY_scan_native.rs.txt').write_text(s);(E/'NIY_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=2)+'\n');pins=json.loads((E/'NIY_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()});(E/'NIY_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
rows=json.loads((E/'NIY_NATIVE_MATRIX.json').read_text())
for name,domain in [('scan_prefix','same proof57607, exact four prefix slice arguments/modes, full8 error replies and arbitrary full tail Result; PREFIX ONLY, not whole canonical_scan'),('scan_m31_step','one actual inner M31 iteration on arbitrary query832/s<4/l<=26, including range exit; pure full Parse/Ok tag, no whole loop'),('scan_opening','actual frozen opening getter; arbitrary i<22/j<832 on SAME proof57607; exact offset10055, descriptor and selected byte')]:
 rows.append(dict(family=name,function='verifier::candidate::NIY_scan_native::'+name,rename='verifier::candidate::NIY_scan_native::'+name+'_renamed',domain=domain,status='planned'))
(E/'NIY_NATIVE_MATRIX.json').write_text(json.dumps(rows,indent=2)+'\n')
(E/'NIY_SCAN_ASSOCIATION.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',candidate_sha256=hashlib.sha256(frozen.encode()).hexdigest(),prefix_source=prefix,prefix_erasure_matches=True,harness_sha256=hashlib.sha256(s.encode()).hexdigest(),status='native boundary candidates; full query-loop association still OPEN'),indent=2)+'\n')
print('Prepared independent canonical_scan prefix/one-M31-iteration/actual-opening candidates; no whole-buffer scan claim.')
