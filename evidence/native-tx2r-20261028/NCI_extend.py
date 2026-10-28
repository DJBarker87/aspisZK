from pathlib import Path
import subprocess,difflib,tempfile,hashlib
E=Path(__file__).resolve().parent

def edit(name,transform):
 path='crates/aspis-r1-cost-probe/src/verifier.rs'
 chain=[];seen=set()
 for p in sorted(E.glob('NCI_K[0-9][0-9][0-9]-harness.patch')):
  h=hashlib.sha256(p.read_bytes()).hexdigest()
  if h not in seen:chain.append(p);seen.add(h)
 paths=set(l[6:] for p in chain for l in p.read_text().splitlines() if l.startswith('+++ b/'))
 with tempfile.TemporaryDirectory(prefix='NCI-gen-') as d:
  for n in paths:
   r=subprocess.run(['git','show','4bb3b3f5:'+n],capture_output=True)
   if r.returncode==0:
    p=Path(d)/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(r.stdout)
  for p in chain:subprocess.run(['git','apply','-'],input=p.read_bytes(),cwd=d,check=True)
  s=(Path(d)/path).read_text()
 (E/name).write_text(''.join(difflib.unified_diff(s.splitlines(True),transform(s).splitlines(True),fromfile='a/'+path,tofile='b/'+path)))

def extend(name,addition):edit(name,lambda s:s+addition)

attrs='''#[kani::proof] #[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,NCI_kmx::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,NCI_kmx::KMX_copy_from_slice)]
'''
if __name__=='__main__':
 h='\n#[cfg(kani)] mod NCI_scalars {\nuse super::*;\n'
 for width,method in [(16,'k'),(32,'e')]:
  for wrong in [False,True]:
   limbs=width//4
   values=','.join(f'u32::from_le_bytes([bytes[start+{4*i}],bytes[start+{4*i+1}],bytes[start+{4*i+2}],bytes[start+{4*i+3}]])' for i in range(limbs))
   h+=attrs+f'''fn {method}_{'wrong' if wrong else 'ok'}(){{
let bytes:[u8;1768]=kani::any();let start:usize=kani::any();kani::assume(start<=1736);
let expected=[{values}];let valid=expected.iter().all(|x|*x<0x7fff_ffff);
let mut r=Reader{{bytes:&bytes,at:start}};let out=r.{method}();
assert!(r.at==start+{width});assert!(r.bytes.as_ptr()==bytes.as_ptr()&&r.bytes.len()==1768);
assert!(out.is_ok(){'!=' if wrong else '=='}valid);
if let Ok(x)=out {{let got={'[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]' if method=='k' else 'x.to_limbs()'};
let j:usize=kani::any();kani::assume(j<{limbs});assert!(got[j]==expected[j]);}}
}}\n'''
 h+='}\n'
 extend('NCI_scalars.patch',h)
