#!/usr/bin/env python3
"""Read only selected native std graph; no new extraction or build."""
import pathlib,subprocess,json,hashlib
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/port23push-20261024'
code=r'''
from pathlib import Path
import hashlib,json
root=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
queries={
'core/src/array/mod.rs':['fn into_iter(self) -> IterMut', 'fn index_mut(&mut self', 'fn as_mut_slice('],
'core/src/slice/mod.rs':['pub const fn iter_mut(', 'pub fn iter_mut('],
'core/src/slice/iter.rs':["pub(super) const fn new(slice: &'a mut [T])", "iterator! {", "fn into_iter(self) -> IterMut"],
'core/src/slice/iter/macros.rs':['fn next(&mut self) -> Option<$elem>'],
'core/src/slice/index.rs':['fn index_mut(self, slice: &mut [T]) -> &mut T', 'fn index(self, slice: &[T]) -> &T'],
'alloc/src/vec/mod.rs':['fn index_mut(&mut self', 'fn deref_mut(&mut self', 'pub const fn as_mut_slice('],
'core/src/iter/range.rs':['fn next(&mut self)', 'fn forward_checked('],
'core/src/convert/num.rs':['macro_rules! impl_from {', 'impl_from!(u32 => u64,']}
rows=[]
for file,needles in queries.items():
 p=root/file;lines=p.read_text().splitlines();hits=[]
 for needle in needles:
  for i,l in enumerate(lines):
   if needle in l:
    end=i;depth=0;seen=False
    for end in range(i,min(len(lines),i+100)):
     depth+=lines[end].count('{')-lines[end].count('}');seen=seen or '{' in lines[end]
     if seen and depth<=0:break
    hits.append(dict(needle=needle,start_line=i+1,end_line=end+1,text='\n'.join(lines[i:end+1])))
 rows.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,hits=hits,unmatched=[n for n in needles if not any(h['needle']==n for h in hits)]))
print(json.dumps(dict(scope='selected extraction-host native std graph, not SBF identity or primitive effect proof',files=rows),indent=2))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True)
(E/'std-source-graph-focused.json').write_text(r.stdout);(E/'std-source-graph-focused-stderr.txt').write_text(r.stderr)
assert r.returncode==0,r.stderr
print(r.stdout)
