#!/usr/bin/env python3
"""Read-only pinned source graph. No extractor/backend command is invoked."""
import hashlib,json,pathlib,subprocess,tarfile,re
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/port21projection-20261024'
code=r'''
from pathlib import Path
import hashlib,json
root=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
queries={
'alloc/src/vec/mod.rs':['pub const fn new()', 'pub fn try_reserve_exact(', 'pub fn resize(', 'fn extend_with('],
'alloc/src/raw_vec/mod.rs':['fn new_in(', 'fn current_memory(', 'fn needs_to_grow(', 'fn try_reserve_exact(', 'fn grow_exact(', 'fn finish_grow(', 'fn set_ptr_and_cap('],
'alloc/src/alloc.rs':['fn alloc_impl(', 'pub unsafe fn alloc(', 'fn allocate(', 'fn grow(', 'fn handle_alloc_error('],
'core/src/alloc/global.rs':['unsafe fn realloc('],
'core/src/array/mod.rs':['fn clone(&self)', 'fn clone_unchecked('],
'core/src/result.rs':['fn map_err<']}
rows=[]
for file,needles in queries.items():
 p=root/file;lines=p.read_text().splitlines();hits=[]
 for needle in needles:
  for i,l in enumerate(lines):
   if needle in l:
    end=i;depth=0;seen=False
    for end in range(i,min(len(lines),i+150)):
     depth+=lines[end].count('{')-lines[end].count('}');seen=seen or '{' in lines[end]
     if seen and depth<=0:break
    hits.append(dict(needle=needle,start_line=i+1,end_line=end+1,text='\n'.join(lines[i:end+1])))
 rows.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,hits=hits))
print(json.dumps(dict(scope='pinned extraction host std source, NOT SBF sysroot or deployed identity',files=rows),indent=2))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True,check=True)
# Original narrower graph is retained separately.
(E/'std-source-graph-complete.json').write_text(r.stdout)
sha=lambda b:hashlib.sha256(b).hexdigest()
base='e2747dd63d2468cff93d5c76880234c5c710defe'
paths=['programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/Cargo.toml','programs/aspis-verifier/Cargo.toml','Cargo.lock']
rows=[]
for path in paths:
 data=subprocess.check_output(['git','show',base+':'+path],cwd=R)
 rows.append(dict(path=path,revision=base,sha256=sha(data),bytes=len(data)))
solana=pathlib.Path('/Users/dominic/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/solana-program-entrypoint-2.3.0')
p=solana/'src/lib.rs';lines=p.read_text().splitlines()
archive=pathlib.Path('/Users/dominic/.cargo/registry/cache/index.crates.io-1949cf8c6b5b557f/solana-program-entrypoint-2.3.0.crate')
lock=subprocess.check_output(['git','show',base+':Cargo.lock'],cwd=R,text=True)
package=next(x for x in lock.split('[[package]]') if 'name = "solana-program-entrypoint"' in x)
checksum=re.search(r'checksum = "([^"]+)"',package)[1]
assert 'version = "2.3.0"' in package and sha(archive.read_bytes())==checksum
with tarfile.open(archive) as tar: assert tar.extractfile('solana-program-entrypoint-2.3.0/src/lib.rs').read()==p.read_bytes()
rows.append(dict(path=str(p),sha256=sha(p.read_bytes()),bytes=p.stat().st_size,lock_package=package,
 package_checksum=checksum,registry_content_checksum_verified=True,
 spans=[dict(start_line=a,end_line=b,text='\n'.join(lines[a-1:b])) for a,b in [(130,142),(222,234),(279,288),(291,365)]]))
(E/'runtime-source-graph.json').write_text(json.dumps(dict(schema='Port21PROJECTION-runtime-source-graph-v1',
 command='python3 tools/port21projection-20261024/Port21PROJECTION_graph.py',script_sha256=sha(pathlib.Path(__file__).read_bytes()),
 source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),files=rows,
 scope='actual cost-probe global allocator declaration and lock-matched SDK; no SBF object identity or native primitive effect proof',
 print_axioms='N/A: source inspection'),indent=2)+'\n')
print(json.dumps(dict(host_source_graph_exit=r.returncode,runtime_package_checksum_verified=True,print_axioms='N/A')))
