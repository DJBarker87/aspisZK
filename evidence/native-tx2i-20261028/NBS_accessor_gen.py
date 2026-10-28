from pathlib import Path
import subprocess,tempfile,difflib,hashlib
E=Path(__file__).resolve().parent;O=E.parent/'native-tx2h-20261028'
chain=[O/n for n in ['NBQ_u06_initial.patch','NBQ_u06b.patch','NBQ_u06c.patch','NBQ_u06d.patch','NBQ_u06e.patch','NBQ_error.patch','NBQ_u07.patch','NBQ_cells.patch','NBQ_tail.patch']]
seen=set()
for p in sorted(E.glob('NBS_K[0-9][0-9][0-9]-harness.patch')):
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if h not in seen:chain.append(p);seen.add(h)
paths=sorted(set(l[6:] for p in chain for l in p.read_text().splitlines() if l.startswith('+++ b/')))
with tempfile.TemporaryDirectory(prefix='NBS-accessor-gen-') as d:
 for n in paths:
  p=Path(d)/n;p.parent.mkdir(parents=True,exist_ok=True);r=subprocess.run(['git','show','4bb3b3f5:'+n],capture_output=True)
  if r.returncode==0:p.write_bytes(r.stdout)
 for p in chain:subprocess.run(['git','apply','-'],input=p.read_bytes(),cwd=d,check=True,capture_output=True)
 name='crates/aspis-r1-cost-probe/src/verifier.rs';s=(Path(d)/name).read_text()
t=r'''
#[cfg(kani)] mod NBS_accessor {
 use super::*;
 #[kani::proof] #[kani::unwind(512)]
 #[kani::stub(<[u8]>::copy_from_slice,crate::NBS_copy::KMX_copy_from_slice)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::NBS_copy::KMX_copy_nonoverlapping)]
 #[kani::stub(<[u8]>::clone_from_slice,crate::NBS_copy::KMX_clone_from_slice)]
 #[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NBS_copy::KMX_extend_from_slice)]
 #[kani::stub(<[u8]>::to_vec,crate::NBS_copy::KMX_to_vec)]
 #[kani::stub(alloc::alloc::realloc,crate::NBS_copy::KMX_realloc)]
 fn all_rows(){
  let rows:[[u32;5];22]=kani::any();
  let mut inverses:Vec<[M31;5]>=rows.map(|r|r.map(M31)).into();
  let count:usize=kani::any();kani::assume(count<=22);inverses.truncate(count);
  let geo=QueryGeometry{start:kani::any(),inverses,line_z:Vec::new()};
  let index:usize=kani::any();kani::assume(index>=geo.start&&index-geo.start<count);
  let offset=index-geo.start;let out=geo.for_query(index);let j:usize=kani::any();kani::assume(j<5);
  assert!(core::ptr::eq(out,&geo.inverses[offset]));assert!(out[j].0==rows[offset][j]);
 }
}
'''
(E/'NBS_accessor.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),(s+t).splitlines(True),fromfile='a/'+name,tofile='b/'+name)))
