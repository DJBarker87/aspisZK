from pathlib import Path
import json,subprocess,tempfile,difflib,hashlib
E=Path(__file__).resolve().parent;O=E.parent/'native-tx2h-20261028'
chain=[O/n for n in ['NBQ_u06_initial.patch','NBQ_u06b.patch','NBQ_u06c.patch','NBQ_u06d.patch','NBQ_u06e.patch','NBQ_error.patch','NBQ_u07.patch','NBQ_cells.patch','NBQ_tail.patch']]
seen=set()
for p in sorted(E.glob('NBS_K[0-9][0-9][0-9]-harness.patch')):
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if h not in seen:chain.append(p);seen.add(h)
paths=sorted(set(l[6:] for p in chain for l in p.read_text().splitlines() if l.startswith('+++ b/')))
with tempfile.TemporaryDirectory(prefix='NBS-generic-fix-') as d:
 for n in paths:
  p=Path(d)/n;p.parent.mkdir(parents=True,exist_ok=True);r=subprocess.run(['git','show','4bb3b3f5:'+n],capture_output=True)
  if r.returncode==0:p.write_bytes(r.stdout)
 for p in chain:subprocess.run(['git','apply','-'],input=p.read_bytes(),cwd=d,check=True,capture_output=True)
 name='crates/aspis-core/src/r0/heap.rs';s=(Path(d)/name).read_text()
 t=s.replace('fn denied(v:&mut Vec<u32>,n:usize)', 'fn denied<T,A:alloc::alloc::Allocator>(v:&mut Vec<T,A>,n:usize)').replace('fn forbidden_resize(_: &mut Vec<u32>,_:usize,_:u32)', 'fn forbidden_resize<T:Clone,A:alloc::alloc::Allocator>(_: &mut Vec<T,A>,_:usize,_:T)')
 assert s!=t
 (E/'NBS_generic_fix.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='a/'+name,tofile='b/'+name)))
