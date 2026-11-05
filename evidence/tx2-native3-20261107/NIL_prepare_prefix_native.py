from pathlib import Path
import subprocess,json,hashlib,difflib
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
path='crates/aspis-r1-cost-probe/src/verifier.rs';src=subprocess.check_output(['git','show',REV+':'+path],text=True)
a=src.index('    if bytes.len()!=checkpoint_size(v)',src.index('pub fn resume<'));z=src.index('    let mut r=Reader{bytes,at:80}',a)
fragment=src[a:z];cut=fragment.replace('bytes[11..16].iter().any(|&b|b!=0)','log.reserved(&bytes[11..16])').replace('hash.digest','log.digest')
s='''use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
struct Log<'a,const C:usize>{bytes:&'a[u8],proof:&'a[u8],public:&'a[u8],replies:[[u8;32];3],header_bad:bool,calls:usize,headers:usize,byte:usize}
impl<'a,const C:usize> Log<'a,C>{
 fn reserved(&mut self,b:&[u8])->bool{let mut pointer=b.as_ptr() as usize;if cfg!(NIL_invert)&&C==0{pointer^=1;}assert_eq!(pointer,self.bytes[11..16].as_ptr() as usize);assert_eq!(b.len(),5);self.headers+=1;let value=if cfg!(NIL_invert)&&C==13{!self.header_bad}else{self.header_bad};if C==13{assert_eq!(value,self.header_bad);}value}
 fn digest(&mut self,parts:&[&[u8]])->[u8;32]{let c=self.calls;assert!(c<3);let mut pointer=parts[if c==2{1}else{0}].as_ptr() as usize;
 if cfg!(NIL_invert)&&((C==2&&c==0)||(C==4&&c==1)){pointer^=1;}
 match c{0=>{assert_eq!(parts.len(),1);assert_eq!(pointer,self.proof.as_ptr() as usize);assert_eq!(parts[0].len(),self.proof.len());},1=>{assert_eq!(parts.len(),1);assert_eq!(pointer,self.public.as_ptr() as usize);assert_eq!(parts[0].len(),self.public.len());},_=>{assert_eq!(parts.len(),2);assert_eq!(pointer,self.bytes.as_ptr() as usize);assert_eq!(parts[1].len(),self.bytes.len()-32);let tag=parts[0];let mut byte=tag[self.byte%22];if cfg!(NIL_invert)&&C==6{byte^=1;}assert_eq!(tag.len(),22);assert_eq!(byte,b"UNPROVED:R1:checkpoint"[self.byte%22]);}}
 self.calls+=1;
 if C>=10&&C<=12&&c==C-10{if cfg!(NIL_invert){assert_eq!(self.calls,c);}else{assert_eq!(self.calls,c+1);}kani::assume(false);}
 let mut out=self.replies[c];if cfg!(NIL_invert)&&((C==1&&c==0)||(C==3&&c==1)||(C==5&&c==2)){out[self.byte]^=1;}
 assert_eq!(out[self.byte],self.replies[c][self.byte]);out
 }
}
fn prefix<const C:usize>(bytes:&[u8],proof:&[u8],public:&[u8],v:Variant,log:&mut Log<C>)->Result<(usize,usize),Error>{
'''+cut+'''Ok((end,bytes[9] as usize))}
fn check<const C:usize>(){
 let bytes:[u8;1768]=kani::any();let proof:[u8;57607]=kani::any();let public:[u8;688]=kani::any();let replies:[[u8;32];3]=kani::any();let header_bad:bool=kani::any();let byte:usize=kani::any();kani::assume(byte<32);
 let early=bytes[..8]==*b"R1P2CKP2"&&bytes[8]==2&&bytes[9]<=22&&bytes[10]==1;
 let valid=early&&!header_bad;let r0=replies[0]==bytes[16..48];let r1=replies[1]==bytes[48..80];let r2=replies[2]==bytes[1736..];
 let mut log=Log::<C>{bytes:&bytes,proof:&proof,public:&public,replies,header_bad,calls:0,headers:0,byte};
 let mut result=prefix(&bytes,&proof,&public,Variant::S2,&mut log);
 if cfg!(NIL_invert){if C==7{result=match result{Ok(_)=>Err(Error::Checkpoint),Err(_)=>Ok((1736,0))};}if C==8{log.calls^=1;}if C==9{if let Ok((end,next))=result{result=Ok((end,next^1));}}}
 let expected_calls=if !valid{0}else if !r0{1}else if !r1{2}else{3};
 assert_eq!(log.calls,expected_calls);assert_eq!(log.headers,if early{1}else{0});
 match result{Ok((end,next))=>{assert!(valid&&r0&&r1&&r2);assert_eq!(end,1736);assert_eq!(next,bytes[9] as usize);assert!(next<=22);},Err(error)=>{assert_eq!(error,Error::Checkpoint);assert!(!(valid&&r0&&r1&&r2));}}
}
'''
rows=[]
for c in range(14):
 n=f'prefix_facet{c}'
 for suffix in ['', '_renamed']:
  s+='#[kani::proof]\n#[kani::unwind(36)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]\nfn '+n+suffix+'(){check::<'+str(c)+'>();}\n'
 rows.append(dict(family=n,function='verifier::NIL_resume_prefix_native::'+n,rename='verifier::NIL_resume_prefix_native::'+n+'_renamed',status='planned',domain='checkpoint1768, proof57607, public688; arbitrary bytes and full digest replies; cached header-any Bool; digest VALUE remains runtime H; abort prefix for C10..12'))
inputs=json.loads((E/'NIL_NATIVE_INPUTS.json').read_text());assert 'mod NIL_resume_prefix_native;' not in inputs[path];inputs[path]+='\n#[cfg(kani)]\n#[path="NIL_resume_prefix_native.rs"]\nmod NIL_resume_prefix_native;\n';inputs['crates/aspis-r1-cost-probe/src/NIL_resume_prefix_native.rs']=s
(E/'NIL_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=2)+'\n');(E/'NIL_resume_prefix_native.rs.txt').write_text(s)
pins=json.loads((E/'NIL_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest() for n,s in inputs.items()});(E/'NIL_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n');(E/'NIL_PREFIX_MATRIX.json').write_text(json.dumps(rows,indent=2)+'\n')
(E/'NIL_PREFIX_NATIVE_CUT.json').write_text(json.dumps(dict(frozen=REV,path=path,fragment=fragment,fragment_sha256=hashlib.sha256(fragment.encode()).hexdigest(),changes=['header-any to LOCAL full Bool recording oracle','digest calls to LOCAL arbitrary reply/abort oracle','cut returns checksum end and SAME header next; original next bounds retained'],missing='Complete header-any native iteration association, primitive reader/tail/Box continuation and caller public688 provenance remain OPEN'),indent=2)+'\n')
patch=''
for n,s in inputs.items():
 try:old=subprocess.check_output(['git','show',REV+':'+n],text=True,stderr=subprocess.DEVNULL)
 except subprocess.CalledProcessError:old=''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NIL_native.patch').write_text(patch)
