"""Read-only capture of deployed source; no compilation or scope launched."""
from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029'
code='''from pathlib import Path
import json,hashlib
root=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src')
names=['slice/iter.rs','slice/mod.rs','slice/index.rs','slice/raw.rs','array/iter.rs','array/iter/iter_inner.rs','array/mod.rs','iter/adapters/zip.rs','iter/traits/iterator.rs','iter/traits/collect.rs','iter/range.rs','ops/index_range.rs','mem/maybe_uninit.rs','mem/manually_drop.rs','ptr/mod.rs','ptr/const_ptr.rs','ptr/metadata.rs','option.rs','mem/maybe_dangling.rs','ub_checks.rs']
rows=[]
for name in names:
 p=root/name;b=p.read_bytes();rows.append(dict(path=str(p),relative=name,sha256=hashlib.sha256(b).hexdigest(),text=b.decode()))
print(json.dumps(rows))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
rows=json.loads(r.stdout)
(E/'library-sources.json').write_text(json.dumps(rows,indent=2)+'\n')
app=[]
for p in ['crates/aspis-core/src/r0/encoder.rs','crates/aspis-core/src/r0/basis.rs','crates/aspis-core/src/r0/scalar.rs','crates/aspis-core/src/field/wide_exact.rs','crates/aspis-r1-cost-probe/src/prover.rs']:
 b=subprocess.check_output(['git','show','HEAD:'+p],cwd=R);app.append(dict(path=p,revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),blob=subprocess.check_output(['git','rev-parse','HEAD:'+p],cwd=R,text=True).strip(),sha256=hashlib.sha256(b).hexdigest(),text=b.decode()))
(E/'application-sources.json').write_text(json.dumps(app,indent=2)+'\n')
print('Read',len(rows),'library files and',len(app),'tracked application files')
