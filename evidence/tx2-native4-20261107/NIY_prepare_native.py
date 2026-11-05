from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-r1-cost-probe/src/verifier.rs'
frozen=subprocess.check_output(['git','show',REV+':'+path],text=True)
segment='let mut r=Reader{bytes,at:80};let state=r.raw();let roots=[r.raw(),r.raw()];'
assert segment in frozen and 'let gamma=r.e()?;' in frozen
s='''use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
fn limb_e(x:E,j:usize)->u32 {let q=if j<4{x.c0()}else{x.c1()};limb_k(q,j&3)}
fn limb_k(q:K,j:usize)->u32 {match j{0=>q.c0.a.0,1=>q.c0.b.0,2=>q.c1.a.0,_=>q.c1.b.0}}
fn word(bytes:&[u8],at:usize)->u32{u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]])}
fn first(bytes:&[u8])->([u8;32],[[u8;32];2],Result<E,Error>,Reader<'_>){
 let mut r=Reader{bytes,at:80};let state=r.raw();let roots=[r.raw(),r.raw()];
 let reply=r.e();(state,roots,reply,r)
}
fn first_check<const C:usize>(){
 let bytes:[u8;1768]=kani::any();let j:usize=kani::any();kani::assume(j<32);
 let (state,roots,reply,r)=first(&bytes);let inv=cfg!(NIY_invert);
 if C==0{assert_eq!(state[j],bytes[80+j]^(if inv{1}else{0}));}
 if C==1{assert_eq!(roots[0][j],bytes[112+j]^(if inv{1}else{0}));}
 if C==2{assert_eq!(roots[1][j],bytes[144+j]^(if inv{1}else{0}));}
 if C==3{assert_eq!(r.at,208^(if inv{1}else{0}));}
 let at=176;
 let good=word(&bytes,at)<0x7fffffff&&word(&bytes,at+4)<0x7fffffff&&word(&bytes,at+8)<0x7fffffff&&word(&bytes,at+12)<0x7fffffff&&word(&bytes,at+16)<0x7fffffff&&word(&bytes,at+20)<0x7fffffff&&word(&bytes,at+24)<0x7fffffff&&word(&bytes,at+28)<0x7fffffff;
 if C==4{assert_eq!(reply.is_ok(),good^inv);if let Err(error)=reply{assert_eq!(error,Error::Checkpoint);}}
 if C==5{if let Ok(value)=reply{assert_eq!(limb_e(value,j&7),word(&bytes,at+4*(j&7))^(if inv{1}else{0}));}}
 if C==6{assert_eq!(r.bytes.as_ptr(),bytes.as_ptr());assert_eq!(r.bytes.len(),1768^(if inv{1}else{0}));}
}
fn e_check<const O:usize,const C:usize>(){
 let bytes:[u8;1768]=kani::any();let j:usize=kani::any();kani::assume(j<8);let mut r=Reader{bytes:&bytes,at:O};let reply=r.e();let inv=cfg!(NIY_invert);
 let good=word(&bytes,O)<0x7fffffff&&word(&bytes,O+4)<0x7fffffff&&word(&bytes,O+8)<0x7fffffff&&word(&bytes,O+12)<0x7fffffff&&word(&bytes,O+16)<0x7fffffff&&word(&bytes,O+20)<0x7fffffff&&word(&bytes,O+24)<0x7fffffff&&word(&bytes,O+28)<0x7fffffff;
 if C==0{assert_eq!(r.at,O+32);assert_eq!(reply.is_ok(),good^inv);if let Err(error)=reply{assert_eq!(error,Error::Checkpoint);}}
 if C==1{assert_eq!(r.bytes.as_ptr(),bytes.as_ptr());assert_eq!(r.bytes.len(),1768);if let Ok(value)=reply{assert_eq!(limb_e(value,j),word(&bytes,O+4*j)^(if inv{1}else{0}));}}
}
fn k_check<const O:usize,const C:usize>(){
 let bytes:[u8;1768]=kani::any();let j:usize=kani::any();kani::assume(j<4);let i:usize=kani::any();kani::assume(i<64);let at=if O==712{712+16*i}else{O};let mut r=Reader{bytes:&bytes,at};let reply=r.k();let inv=cfg!(NIY_invert);
 let good=word(&bytes,at)<0x7fffffff&&word(&bytes,at+4)<0x7fffffff&&word(&bytes,at+8)<0x7fffffff&&word(&bytes,at+12)<0x7fffffff;
 if C==0{assert_eq!(r.at,at+16);assert_eq!(reply.is_ok(),good^inv);if let Err(error)=reply{assert_eq!(error,Error::Checkpoint);}}
 if C==1{assert_eq!(r.bytes.as_ptr(),bytes.as_ptr());assert_eq!(r.bytes.len(),1768);if let Ok(value)=reply{assert_eq!(limb_k(value,j),word(&bytes,at+4*j)^(if inv{1}else{0}));}}
}
'''
rows=[]
for name,call,domain in [(f'first{c}',f'first_check::<{c}>();','arbitrary checkpoint1768, same reader at80, actual raw32/raw32/raw32/e; selected byte/limb') for c in range(7)]+[(f'e{o}_{c}',f'e_check::<{o},{c}>();',f'arbitrary checkpoint1768, SAME reader at{o}, actual one E read') for o in [176,208,240,272,632,664] for c in range(2)]+[(f'k{o}_{c}',f'k_check::<{o},{c}>();',f'arbitrary checkpoint1768, SAME reader at{o}' + ('+16*i, i<64, one weight iteration' if o==712 else '')+', actual one K read') for o in [304,568,584,600,616,696,712] for c in range(2)]:
 for suffix in ['', '_renamed']:
  s+='#[kani::proof]\n#[kani::unwind(36)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]\nfn '+name+suffix+'(){'+call+'}\n'
 rows.append(dict(family=name,function='verifier::NIY_tail_native::'+name,rename='verifier::NIY_tail_native::'+name+'_renamed',domain=domain,status='planned'))
x=json.loads((E/'NIY_NATIVE_INPUTS.json').read_text());assert 'mod NIY_tail_native;' not in x[path]
x[path]+='\n#[cfg(kani)]\n#[path="NIY_tail_native.rs"]\nmod NIY_tail_native;\n';x['crates/aspis-r1-cost-probe/src/NIY_tail_native.rs']=s
(E/'NIY_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=2)+'\n');(E/'NIY_tail_native.rs.txt').write_text(s)
pins=json.loads((E/'NIY_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(v.encode()).hexdigest() for n,v in x.items()});(E/'NIY_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
(E/'NIY_NATIVE_MATRIX.json').write_text(json.dumps(rows,indent=2)+'\n')
patch=''
for n,v in x.items():
 try:old=subprocess.check_output(['git','show',REV+':'+n],text=True,stderr=subprocess.DEVNULL)
 except subprocess.CalledProcessError:old=''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),v.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NIY_native.patch').write_text(patch)
(E/'NIY_NATIVE_ASSOCIATION.json').write_text(json.dumps(dict(frozen_revision=REV,frozen_verifier_sha256=hashlib.sha256(frozen.encode()).hexdigest(),frozen_segment=segment,first_read='r.e()',native_sha256=hashlib.sha256(s.encode()).hexdigest(),kind='source-cut transcription; not a parent theorem',copy_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'),indent=2)+'\n')
p=E/'NIY_run.py';t=p.read_text().replace("' --cfg NIL_invert'","' --cfg NIL_invert --cfg NIY_invert'");p.write_text(t)
print('Prepared 33 native facet families with matched corruption and rename cases; one native iteration for weight reads, no field multiplication.')
