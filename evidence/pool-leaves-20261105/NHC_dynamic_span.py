"""Valid zero-initialized dynamic span geometry; tail-value generality is NOT assumed."""
from pathlib import Path
import sys,subprocess,difflib,json
E=Path(__file__).resolve().parent;family,mode=sys.argv[1:3];assert family in ['forward','iterate'] and mode in ['positive','negative']
bound_bits=int(sys.argv[3]) if len(sys.argv)>3 else None
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';read=lambda p:subprocess.check_output(['git','show',rev+':'+p],text=True)
s='''use super::*;
#[kani::proof]
#[kani::unwind(33)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NFO_KMX::KMX_realloc)]
fn association(){
 let n:usize=kani::any();kani::assume(n>0&&n<=isize::MAX as usize);
 let layout=core::alloc::Layout::from_size_align(n,1).unwrap();
 let pointer=unsafe{alloc::alloc::alloc_zeroed(layout)};kani::assume(!pointer.is_null());
 {
  let i:usize=kani::any();kani::assume(i<n);let byte:u8=kani::any();unsafe{pointer.add(i).write(byte);}
  let whole=unsafe{core::slice::from_raw_parts(pointer,n)};
  let suffix=&whole[i..];
'''
if family=='forward':
 s+='''let mut calls=0;let mut observed=None;
 let mut opaque=|arg:&[u8]|{calls+=1;observed=Some((arg.as_ptr(),arg.len()));Err::<(),ProgramError>(ProgramError::InvalidInstructionData)};
 let result=opaque(suffix);
'''
 if mode=='negative':s+='if let Some((p,len))=observed{observed=Some((p,len^1));}\n'
 s+='assert!(calls==1);assert!(observed==Some((pointer.wrapping_add(i) as *const u8,n-i)));assert!(matches!(result,Err(ProgramError::InvalidInstructionData)));\n'
else:
 s+='let mut iter=suffix.iter();let mut observed=iter.next().map(|b|(*b,b as *const u8));let mut remaining=iter.as_slice().len();\n'
 if mode=='negative':s+='remaining^=1;\n'
 s+='assert!(observed==Some((byte,pointer.wrapping_add(i) as *const u8)));assert!(remaining==n-i-1);assert!(iter.as_slice().as_ptr()==pointer.wrapping_add(i+1));\n'
if bound_bits is not None:s=s.replace('n<=isize::MAX as usize','n<=(1usize<<'+str(bound_bits)+')')
s+=' }\n unsafe{alloc::alloc::dealloc(pointer,layout);}\n}\n';patch=''
for p in ['programs/aspis-pool/src/pair_forest.rs','programs/aspis-pool/src/lib.rs']:
 f=read(p);after=f+'\n#[cfg(kani)]\n#[path="NHC_DynamicSpan.rs"]\nmod NHC_DynamicSpan;\n' if p.endswith('pair_forest.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+f+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(f.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NHC_DynamicSpan.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in s.splitlines())
(E/'NHC_native.patch').write_text(patch);(E/'NHC_CURRENT.json').write_text(json.dumps(dict(kind='unbounded physical span '+family,mode=mode,source=s,domain=('returning valid dynamic allocations 1..'+('2^'+str(bound_bits) if bound_bits is not None else 'isize::MAX')+', arbitrary selected offset and byte; other bytes initialized zero; NOT an arbitrary-tail-value certificate'),diagnostic_bound_bits=bound_bits,modifies=['fresh private harness allocation','local iterator and records'],production_credit=False,remaining='allocator/tool support, arbitrary-tail noninterference and caller physical interpretation'),indent=1)+'\n')
print('pair_forest::NHC_DynamicSpan::association')
