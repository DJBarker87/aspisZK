"""Read-only Rust 1.94.1 allocator/capacity source receipt, no execution gate.
This inventory records source, not a native association acceptance claim.
"""
from pathlib import Path
import subprocess,shlex,json,sys,hashlib
E=Path('evidence/pv-evh8-20261101');root='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/'
selections={'alloc/src/raw_vec/mod.rs':[(24,34),(410,473),(850,880)],'alloc/src/alloc.rs':[(180,216),(420,441),(525,574)]}
code='''import pathlib,hashlib,json
root=pathlib.Path(ROOT);selections=SELECTIONS
rows=[]
for name,spans in selections.items():
 p=root/name;raw=p.read_bytes();lines=raw.decode().splitlines(keepends=True)
 rows.append(dict(path=str(p),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),spans=[dict(first=a,last=b,text=''.join(lines[a-1:b])) for a,b in spans]))
print(json.dumps(dict(toolchain_directory='1.94.1-x86_64-unknown-linux-gnu',files=rows)))
'''.replace('ROOT',repr(root)).replace('SELECTIONS',repr(selections))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True,capture_output=True);assert r.returncode==0,r.stderr
x=json.loads(r.stdout);x.update(status='READ-ONLY deployed-library source inventory; structural binding OPEN',model='PV_EVH_AllocatorWorld',obligations=['RawVec layout and zero-size branch','allocator state/errno/address validity','initialized regions and ownership','capacity overflow and handle_alloc_error diagnostic/abort paths under fmt-1','native event encoding','V370 compiler boundary'],rows_removed=[])
out=json.dumps(x,indent=2)+'\n';p=E/'allocator-sources.json'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
print('Read-only source receipt:',len(x['files']),'Rust 1.94.1 files; native association OPEN')
