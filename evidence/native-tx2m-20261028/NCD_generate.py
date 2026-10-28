from pathlib import Path
import subprocess,tempfile,hashlib,difflib
E=Path(__file__).resolve().parent;I=E.parent/'native-tx2i-20261028';Q=E.parent/'native-tx2h-20261028'
def current(name):
 base=[Q/n for n in ['NBQ_u06_initial.patch','NBQ_u06b.patch','NBQ_u06c.patch','NBQ_u06d.patch','NBQ_u06e.patch','NBQ_error.patch','NBQ_u07.patch','NBQ_cells.patch','NBQ_tail.patch']]
 seen=set();chain=base[:]
 for p in sorted(I.glob('NBS_K[0-9][0-9][0-9]-harness.patch'))+sorted((E.parent/'native-tx2l-20261028').glob('NCB_K[0-9][0-9][0-9]-harness.patch'))+sorted(E.glob('NCD_K[0-9][0-9][0-9]-harness.patch')):
  h=hashlib.sha256(p.read_bytes()).hexdigest()
  if h not in seen:seen.add(h);chain.append(p)
 paths=sorted(set(l[6:] for p in chain for l in p.read_text().splitlines() if l.startswith('+++ b/'))|{name})
 with tempfile.TemporaryDirectory() as d:
  for n in paths:
   q=Path(d)/n;q.parent.mkdir(parents=True,exist_ok=True);r=subprocess.run(['git','show','4bb3b3f5:'+n],capture_output=True)
   if r.returncode==0:q.write_bytes(r.stdout)
  for p in chain:subprocess.run(['git','apply','-'],input=p.read_bytes(),cwd=d,capture_output=True,check=True)
  return (Path(d)/name).read_text()
def emit(name,text,label):
 s=current(name);(E/(label+'.patch')).write_text(''.join(difflib.unified_diff(s.splitlines(True),(s+text).splitlines(True),fromfile='a/'+name,tofile='b/'+name)))
attrs='\n'.join(['#[kani::stub(<[u8]>::copy_from_slice,crate::NBS_copy::KMX_copy_from_slice)]','#[kani::stub(core::ptr::copy_nonoverlapping,crate::NBS_copy::KMX_copy_nonoverlapping)]','#[kani::stub(<[u8]>::clone_from_slice,crate::NBS_copy::KMX_clone_from_slice)]','#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NBS_copy::KMX_extend_from_slice)]','#[kani::stub(<[u8]>::to_vec,crate::NBS_copy::KMX_to_vec)]','#[kani::stub(alloc::alloc::realloc,crate::NBS_copy::KMX_realloc)]'])+'\n'
if __name__=='__main__':
 text='''\n#[cfg(kani)] mod NCD_resize {
 use super::*;
 #[kani::proof] #[kani::unwind(32)]
 ATTR fn copy_negative(){
  let a:[u32;16]=[0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,512];let mut b=[0u32;16];
  b.copy_from_slice(&a);assert!(b[15]==0);
 }
 #[kani::proof] #[kani::unwind(32)]
 ATTR fn byte_one(){
  let old:u8=kani::any();let value:u8=kani::any();let n:usize=kani::any();kani::assume(n<=1);
  let mut out=Vec::<u8>::with_capacity(2);if n==1{out.push(old);}
  let ptr=out.as_ptr();let cap=out.capacity();out.resize(n+1,value);
  assert!(out.len()==n+1&&out.capacity()==cap&&out.as_ptr()==ptr);
  let j:usize=kani::any();kani::assume(j<=n);assert!(out[j]==if j<n{old}else{value});
 }
 #[kani::proof] #[kani::unwind(32)]
 ATTR fn word_one(){
  let old:u32=kani::any();let value:u32=kani::any();let n:usize=kani::any();kani::assume(n<=1);
  let mut out=Vec::<u32>::with_capacity(2);if n==1{out.push(old);}
  let ptr=out.as_ptr();let cap=out.capacity();out.resize(n+1,value);
  assert!(out.len()==n+1&&out.capacity()==cap&&out.as_ptr()==ptr);
  let j:usize=kani::any();kani::assume(j<=n);assert!(out[j]==if j<n{old}else{value});
 }
}
'''.replace('ATTR',attrs)
 emit('crates/aspis-core/src/r0/heap.rs',text,'NCD_resize')
