from pathlib import Path
import json,subprocess,hashlib,difflib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
x={}
for n in ['lib.rs','verifier.rs']:
 p='crates/aspis-r1-cost-probe/src/'+n;x[p]=subprocess.check_output(['git','show',rev+':'+p],text=True)
# The exact KMX patch adds its modules to lib.rs. Reproduce those bytes from the pinned patch itself.
p=Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
for line in p.splitlines():
 if line.startswith('+') and not line.startswith('+++') and ('mod KMX_' in line or 'use KMX_' in line or '#[cfg(kani)]' in line):pass
# Read patched lib bytes from the already staged scratch without modifying them.
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat /home/dombarker/project-offloads/codex-cx-tx2-native5-20261107/NJC_src/crates/aspis-r1-cost-probe/src/lib.rs'],capture_output=True,text=True);assert r.returncode==0
x['crates/aspis-r1-cost-probe/src/lib.rs']=subprocess.check_output(['git','show',rev+':crates/aspis-r1-cost-probe/src/lib.rs'],text=True).replace('#![no_std]','#![no_std]\n#![cfg_attr(kani,feature(allocator_api))]')+'\n#[cfg(kani)] include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n' 
s='''use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
fn word(bytes:&[u8],at:usize)->u32{u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]])}
fn kw(q:K)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn raw<const N:usize>(){
 let bytes:[u8;32]=kani::any();let at=0usize;
 let mut r=Reader{bytes:&bytes,at};let out=r.raw::<N>();
 let mut i=0;while i<N{assert_eq!(out[i],bytes[at+i]^(if cfg!(NJC_invert){1}else{0}));i+=1;}
 assert_eq!(r.at,at+N);assert_eq!(r.bytes.as_ptr(),bytes.as_ptr());assert_eq!(r.bytes.len(),32);
}
fn read_k(){
 let bytes:[u8;16]=kani::any();let at=0usize;
 let expected=[word(&bytes,at),word(&bytes,at+4),word(&bytes,at+8),word(&bytes,at+12)];
 let good=expected[0]<2147483647&&expected[1]<2147483647&&expected[2]<2147483647&&expected[3]<2147483647;
 let mut r=Reader{bytes:&bytes,at};let result=r.k();
 assert_eq!(result.is_ok(),good^cfg!(NJC_invert));
 match result{Ok(q)=>assert_eq!(kw(q),expected),Err(e)=>assert_eq!(e,Error::Checkpoint)}
 assert_eq!(r.at,at+16);assert_eq!(r.bytes.as_ptr(),bytes.as_ptr());assert_eq!(r.bytes.len(),16);
}
fn read_e(){
 let bytes:[u8;32]=kani::any();let at=0usize;
 let expected=[word(&bytes,at),word(&bytes,at+4),word(&bytes,at+8),word(&bytes,at+12),word(&bytes,at+16),word(&bytes,at+20),word(&bytes,at+24),word(&bytes,at+28)];
 let good=expected[0]<2147483647&&expected[1]<2147483647&&expected[2]<2147483647&&expected[3]<2147483647&&expected[4]<2147483647&&expected[5]<2147483647&&expected[6]<2147483647&&expected[7]<2147483647;
 let mut r=Reader{bytes:&bytes,at};let result=r.e();
 assert_eq!(result.is_ok(),good^cfg!(NJC_invert));
 match result{Ok(q)=>assert_eq!(q.to_limbs(),expected),Err(e)=>assert_eq!(e,Error::Checkpoint)}
 assert_eq!(r.at,at+32);assert_eq!(r.bytes.as_ptr(),bytes.as_ptr());assert_eq!(r.bytes.len(),32);
}
'''
for name,call in [('raw4','raw::<4>()'),('raw16','raw::<16>()'),('raw32','raw::<32>()'),('k','read_k()'),('e','read_e()')]:
 for suffix in ['','_renamed']:
  s+='''#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn '''+name+suffix+'(){'+call+';}\n'
x['crates/aspis-r1-cost-probe/src/verifier.rs']+='\n#[cfg(kani)]\n#[path="NJC_readers.rs"]\nmod NJC_readers;\n';x['crates/aspis-r1-cost-probe/src/NJC_readers.rs']=s
for n in subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'tools/r1-builder-reference'],text=True).splitlines():
 if n.endswith('.rs'):x[n]=subprocess.check_output(['git','show',rev+':'+n],text=True)
(E/'NJC_readers.rs.txt').write_text(s);(E/'NJC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n')
manifest=json.loads(subprocess.check_output(['git','show','HEAD:evidence/extract-stage-20261106/NHR_STAGING_MANIFEST.json'],text=True));pins={n:v['sha256'] for n,v in manifest['files'].items()}
pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()})
(E/'NJC_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=''
for n,t in x.items():
 z=subprocess.run(['git','show',rev+':'+n],capture_output=True,text=True);old=z.stdout if z.returncode==0 else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),t.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NJC_native.patch').write_text(patch)
