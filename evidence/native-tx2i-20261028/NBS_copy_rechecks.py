from pathlib import Path
import subprocess,json,re,tempfile,difflib,hashlib
E=Path(__file__).resolve().parent;O=E.parent/'native-tx2h-20261028'
base=[O/n for n in ['NBQ_u06_initial.patch','NBQ_u06b.patch','NBQ_u06c.patch','NBQ_u06d.patch','NBQ_u06e.patch','NBQ_error.patch','NBQ_u07.patch','NBQ_cells.patch','NBQ_tail.patch']]
seen=set();own=[]
for p in sorted(E.glob('NBS_K[0-9][0-9][0-9]-harness.patch')):
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if h not in seen:seen.add(h);own.append(p)
core='crates/aspis-core';r1='crates/aspis-r1-cost-probe'
# Reserve-denied is a new run; the remainder recheck passing properties.
rows=[
(25,core,'r0::heap::NBS_buffer','reserve_denied','r0/heap.rs',512),
(26,core,'r0::heap::NBS_filled','one_qm31','r0/heap.rs',512),
(27,r1,'fast_dots::NBS_joined','eight_cells','fast_dots.rs',512),
(28,r1,'fast_dots::NBS_joined','eight_folds','fast_dots.rs',512),
(29,r1,'fast_dots::NBS_tail','complete_tail','fast_dots.rs',2048),
(30,r1,'fast_domain::NBS_route','fibre','fast_domain.rs',8192),
(31,r1,'fast_domain::NBS_route','line','fast_domain.rs',8192),
(32,r1,'verifier::NBS_geometry_cuts','prefix_write','verifier.rs',512),
(33,r1,'verifier::NBS_geometry_cuts','backward_write','verifier.rs',512),
(34,r1,'verifier::NBS_geometry','group_pack','verifier.rs',512),
(35,r1,'verifier::NBS_geometry','query_accessor','verifier.rs',512),
(36,r1,'verifier::NBS_geometry','nonzero_guard','verifier.rs',512),
(37,r1,'verifier::NBS_geometry','empty_range','verifier.rs',512),
(38,r1,'verifier::NBS_geometry','invalid_range','verifier.rs',512),
(39,r1,'verifier::NBS_geometry','reverse_first','verifier.rs',512)]
paths=sorted(set([l[6:] for p in base+own for l in p.read_text().splitlines() if l.startswith('+++ b/')]+[core+'/src/lib.rs',r1+'/src/lib.rs']))
patch=(E/'NBS_KMX_KMX_copy_stubs.patch').read_text().split('diff --git a/KMX_native.rs',1)[0]
stub=''.join(l[1:] for l in patch.splitlines(True) if l.startswith('+') and not l.startswith('+++')).split('#[cfg(kani)]',1)[0]
attrs='\n'.join([
'#[kani::stub(<[u8]>::copy_from_slice,crate::NBS_copy::KMX_copy_from_slice)]',
'#[kani::stub(core::ptr::copy_nonoverlapping,crate::NBS_copy::KMX_copy_nonoverlapping)]',
'#[kani::stub(<[u8]>::clone_from_slice,crate::NBS_copy::KMX_clone_from_slice)]',
'#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NBS_copy::KMX_extend_from_slice)]',
'#[kani::stub(<[u8]>::to_vec,crate::NBS_copy::KMX_to_vec)]',
'#[kani::stub(alloc::alloc::realloc,crate::NBS_copy::KMX_realloc)]'])+'\n'
with tempfile.TemporaryDirectory(prefix='NBS-copy-hooks-') as d:
 for name in paths:
  p=Path(d)/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(subprocess.check_output(['git','show','4bb3b3f5:'+name]))
 for p in base+own:subprocess.run(['git','apply','-'],input=p.read_bytes(),cwd=d,check=True,capture_output=True)
 before={name:(Path(d)/name).read_text() for name in paths}
 for crate in [core,r1]:
  name=crate+'/src/lib.rs';p=Path(d)/name;s=p.read_text().replace('#![no_std]','#![no_std]\n#![cfg_attr(kani, feature(allocator_api))]',1).replace('extern crate alloc;','extern crate alloc;\n#[cfg(kani)] mod NBS_copy;',1);p.write_text(s)
  name=crate+'/src/NBS_copy.rs';before[name]='';(Path(d)/name).write_text(stub)
 recorded=[]
 for n,crate,namespace,fn,file,bound in rows:
  path=crate+'/src/'+file;p=Path(d)/path;s=p.read_text()
  m=re.search(r'\bfn\s+'+re.escape(fn)+r'\s*\(',s);assert m,(fn,path)
  start=s.rfind('#[kani::proof]',0,m.start());assert start>=0
  brace=s.index('{',m.end());depth=1;end=brace+1
  while depth:
   depth+=(s[end]=='{')-(s[end]=='}');end+=1
  old=s[start:end];new=re.sub(r'#\[kani::unwind\(\d+\)\]',f'#[kani::unwind({bound})]',old)
  new=re.sub(r'\bfn\s+'+re.escape(fn)+r'\s*\(',attrs+f'fn NBS_recheck_{n}(',new,count=1)
  original_body=s[brace:end];new_body=new[new.index('{'):]
  assert original_body==new_body,'property/assumption drift'
  s=s[:end]+'\n\n'+new+'\n'+s[end:];p.write_text(s)
  recorded.append(dict(run=n,crate=crate,harness=namespace+f'::NBS_recheck_{n}',original_harness=namespace+'::'+fn,unwind=bound,property_body_sha256=hashlib.sha256(original_body.encode()).hexdigest(),property_unchanged=True))
 out=''
 for name,old in before.items():
  new=(Path(d)/name).read_text()
  if old!=new:out+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+name if old else '/dev/null',tofile='b/'+name))
 (E/'NBS_copy_hooks.patch').write_text(out)
 (E/'NBS_COPY_RECHECK_PLAN.json').write_text(json.dumps(dict(rechecks=recorded,stub_body_sha256=hashlib.sha256(stub.encode()).hexdigest(),source='NBS_KMX_IMPORT.json',qualification='same original properties and assumptions; additional validated value-copy hooks; adequate element/reallocation-prefix bounds; no capacity/pointer/ownership refinement claimed from KMX'),indent=2)+'\n')
