from pathlib import Path
import subprocess,difflib,tempfile
E=Path(__file__).resolve().parent;src='crates/aspis-r1-cost-probe/src/fast_pairing.rs';base=subprocess.check_output(['git','show','4bb3b3f5:'+src],text=True)
with tempfile.TemporaryDirectory() as d:
 q=Path(d)/src;q.parent.mkdir(parents=True);q.write_text(base)
 for p in ['NBQ_u06_initial.patch','NBQ_u06b.patch','NBQ_u06c.patch','NBQ_u06d.patch']:subprocess.run(['git','apply','-'],cwd=d,input=(E/p).read_text(),text=True,check=True)
 old=q.read_text()
s=old.replace('static mut CALLS:usize=0;','static mut CALLS:usize=0;\n static mut PTR0:*mut canonical::Dot=core::ptr::null_mut(); static mut PTR1:*mut canonical::Dot=core::ptr::null_mut();')
s=s.replace('assert!(CALLS<2);','assert!(CALLS<2);assert!(core::ptr::eq(d,if CALLS==0{PTR0}else{PTR1}));')
s=s.replace('unsafe{CALLS=0;WANT0=', 'unsafe{PTR0=&mut d.c0;PTR1=&mut d.c1;CALLS=0;WANT0=')
(E/'NBQ_u06e.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+src,tofile='b/'+src)))
