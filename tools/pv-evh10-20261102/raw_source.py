"""Read-only snapshot of the adopted Linux raw getrandom dependency cone."""
from pathlib import Path
import json,subprocess,shlex,hashlib,sys
E=Path('evidence/pv-evh10-20261102')
code='''from pathlib import Path
import json,hashlib
root=next(Path('/home/dombarker/.cargo/registry/src').glob('*/getrandom-0.3.4'))
names=['Cargo.toml','build.rs','src/lib.rs','src/util.rs','src/error.rs','src/backends.rs','src/backends/linux_raw.rs','src/backends/sanitizer.rs']
print(json.dumps([dict(path=str(root/n),relative=n,sha256=hashlib.sha256((root/n).read_bytes()).hexdigest(),text=(root/n).read_text()) for n in names]))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True,capture_output=True)
assert r.returncode==0,r.stderr
rows=json.loads(r.stdout)
p=E/'getrandom-034-linux-raw-source.json'
if '--check' in sys.argv: assert json.load(open(p))==rows
else:p.write_text(json.dumps(rows,indent=2)+'\n')
print('PASS deployed getrandom0.3.4 source snapshot (read-only)')
