from NCB_generate import *
p='programs/r1-cost-probe/src/lib.rs';s=current(p);t=s.replace('static mut PARTS:*const &[u8]=core::ptr::null();','static mut PARTS:*const ()=core::ptr::null();').replace('core::ptr::eq(parts.as_ptr(),PARTS)','core::ptr::eq(parts.as_ptr().cast::<()>(),PARTS)').replace('PARTS=parts.as_ptr();','PARTS=parts.as_ptr().cast::<()>();')
assert t!=s
(E/'NCB_digest_lifetime.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
