from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-fxmem-20261028'
b='/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/alloc/src/'
paths={k:b+v for k,v in dict(vec='vec/mod.rs',raw='raw_vec/mod.rs',alloc='alloc.rs').items()}
code='from pathlib import Path\nimport json\nprint(json.dumps({k:Path(p).read_text() for k,p in '+repr(paths)+'.items()}))'
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
s=json.loads(r.stdout)
src=(R/'tools/pv-fxmem-20261028/structural-drop.py').read_text();exec(src[src.index('def clean('):src.index('expected=')])
rows=[]
for k,anchor in [('vec','pub fn try_reserve_exact('),('raw','pub(crate) fn try_reserve_exact('),('raw','unsafe fn try_reserve_exact('),('raw','unsafe fn grow_exact('),('raw','fn needs_to_grow('),('raw','fn finish_grow('),('raw','unsafe fn set_ptr_and_cap('),('alloc','fn alloc_impl_runtime('),('alloc','fn grow_impl_runtime('),('raw','fn layout_array(')]:
 try:actual=body(s[k],anchor)
 except ValueError:continue
 rows.append(dict(file=paths[k],file_sha256=hashlib.sha256(s[k].encode()).hexdigest(),anchor=anchor,body=actual))
(E/'RESERVE-SOURCE.json').write_text(json.dumps(rows,indent=2)+'\n')
for x in rows:print(x['anchor'],x['body'])
