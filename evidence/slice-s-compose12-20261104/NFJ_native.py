"""One retained-allocation/slot forwarding cut; no symbolic buffer equality."""
from pathlib import Path
import subprocess,difflib,json,sys
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
mode=sys.argv[1]
assert mode in ['positive','left','right','size','slot','reply','branch','frame','copy','copy-negative','header','header-negative','retained','retained-negative']
source=r'''use super::*;
struct Frame { left:*const u8,right:*const u8,slot:*mut i32,reply:i32,calls:u8,j:usize,left_byte:u8,right_byte:u8 }
// Runtime value is opaque here. RuntimeMemcmp(ac) supplies its zero law in Lean.
fn runtime(left:&[u8],right:&[u8],n:usize,slot:&mut i32,f:&mut Frame){
 assert!(f.calls==0);
 assert!(core::ptr::eq(left.as_ptr(),f.left)&&left.len()==688);
 assert!(core::ptr::eq(right.as_ptr(),f.right)&&right.len()==688);
 assert!(n==688&&core::ptr::eq(slot as *mut i32,f.slot));
 assert!(left[f.j]==f.left_byte&&right[f.j]==f.right_byte);
 f.calls=1;*slot=f.reply;
}
fn different(left:&[u8],right:&[u8],f:&mut Frame)->bool{
 let mut slot:i32=0;f.slot=&mut slot;
 runtime(left,right,688,&mut slot,f);
 slot!=0
}
fn continuation(encoded:&[u8;688],candidate_bytes:&[u8;688],tag:u8,f:&mut Frame)->bool{
 if different(encoded.as_ref(),candidate_bytes,f) || tag!=Variant::S2.tag(){return false;}true
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFJ_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFJ_KMX::KMX_copy_from_slice)]
fn same_buffers(){
 let left:[u8;688]=kani::any();let right:[u8;688]=kani::any();let reply:i32=kani::any();let tag:u8=kani::any();
 let j:usize=kani::any();kani::assume(j<688);
 let mut f=Frame{left:left.as_ptr(),right:right.as_ptr(),slot:core::ptr::null_mut(),reply,calls:0,j,left_byte:left[j],right_byte:right[j]};
 let result=continuation(&left,&right,tag,&mut f);
 assert!(f.calls==1&&result==(reply==0&&tag==2));
 assert!(left[j]==f.left_byte&&right[j]==f.right_byte&&f.reply==reply);
}
'''
if mode=='left':source=source.replace('runtime(left,right,688','runtime(right,right,688')
if mode=='right':source=source.replace('runtime(left,right,688','runtime(left,left,688')
if mode=='size':source=source.replace('runtime(left,right,688','runtime(left,right,687')
if mode=='slot':source=source.replace('f.slot=&mut slot;','let mut other:i32=0;f.slot=&mut other;')
if mode=='reply':source=source.replace('slot!=0','slot==0')
if mode=='branch':source=source.replace('|| tag!=Variant','&& tag!=Variant')
if mode=='frame':source=source.replace('&&f.reply==reply','&&f.reply!=reply')
if mode.startswith('copy'):
 source='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFJ_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFJ_KMX::KMX_copy_from_slice)]
fn same_buffers(){let b:u8=kani::any();let a=[b];let mut d=[0u8];d.copy_from_slice(&a);assert!(d[0]=='''+('b^1' if mode=='copy-negative' else 'b')+');}\n'
if mode.startswith('header'):
 source='use super::*;\n#[kani::proof]\nfn same_buffers(){let bytes:[u8;688]=kani::any();let candidate_start=0;let proof_start=candidate_start+POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;let candidate_bytes=&bytes[candidate_start..proof_start];assert!(candidate_bytes.len()==688&&core::ptr::eq(candidate_bytes.as_ptr(),'+('unsafe{bytes.as_ptr().add(1)}' if mode=='header-negative' else 'bytes.as_ptr()')+'));}\n'
if mode.startswith('retained'):
 source='use super::*;\nstruct Frame{calls:u8,reply:i32,left:*const u8,right:*const u8}\nfn compare(a:&[u8],b:&[u8],f:&mut Frame)->bool{assert!(f.calls==0&&a.len()==688&&b.len()==688&&core::ptr::eq(a.as_ptr(),f.left)&&core::ptr::eq(b.as_ptr(),f.right));f.calls=1;f.reply!=0}\n#[kani::proof]\nfn same_buffers(){let encoded:[u8;688]=kani::any();let header:[u8;688]=kani::any();let mut f=Frame{calls:0,reply:kani::any(),left:encoded.as_ptr(),right:header.as_ptr()};let different=compare(encoded.as_ref(),&header,&mut f);assert!(f.calls==1&&different==(f.reply!=0));}\n'
 if mode=='retained-negative':source=source.replace('compare(encoded.as_ref(),&header','compare(header.as_ref(),&header')
p='programs/r1-cost-probe/src/r1_pool_adapter.rs';frozen=subprocess.check_output(['git','show',REV+':'+p],text=True)
hook=frozen+'\n#[cfg(kani)]\n#[path="NFJ_scan.rs"]\nmod NFJ_scan;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/programs/r1-cost-probe/src/NFJ_scan.rs\n@@ -0,0 +1,'+str(len(source.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in source.splitlines())
p='programs/r1-cost-probe/src/lib.rs';frozen=subprocess.check_output(['git','show',REV+':'+p],text=True)
hook='#![cfg_attr(kani, feature(allocator_api))]\n'+frozen+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFJ_KMX;\n'
patch+=''.join(difflib.unified_diff(frozen.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
(E/'NFJ_native.patch').write_text(patch)
(E/'NFJ_CURRENT.json').write_text(json.dumps(dict(mode=mode,source=source,classification='local retained-allocation/slot oracle forwarding; runtime value law supplied ONLY by explicit RuntimeMemcmp(ac)'),indent=1)+'\n')
