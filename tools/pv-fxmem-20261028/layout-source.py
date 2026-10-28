from pathlib import Path
import json,hashlib,subprocess,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-fxmem-20261028'
p='/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/alloc/layout.rs'
r=subprocess.run(['ssh','dombarker@100.108.41.90','cat '+p],text=True,capture_output=True);assert r.returncode==0,r.stderr
s=r.stdout;src=(R/'tools/pv-fxmem-20261028/structural-drop.py').read_text();exec(src[src.index('def clean('):src.index('expected=')])
rows=[]
for anchor in ['pub const fn repeat_packed(', 'fn max_size_for_alignment(', 'const fn is_size_alignment_valid(', 'const fn from_size_alignment(']:
 try:b=body(s,anchor)
 except ValueError:continue
 rows.append(dict(anchor=anchor,body=b));print(anchor,b)
(E/'LAYOUT-SOURCE.json').write_text(json.dumps(dict(path=p,sha256=hashlib.sha256(s.encode()).hexdigest(),bodies=rows),indent=2)+'\n')
