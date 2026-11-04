"""Read-only collection from the deployed-version rust-src; no build/run.

The source package is input evidence, not proof that the adopted binary was
compiled from these bytes. The latter stays at the named V370 boundary.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

E = Path('evidence/pv-evhB-20261103')
DEST = E/'inputs/std-1.94.1-D588'
FILES = ['alloc/src/alloc.rs', 'std/src/alloc.rs',
         'std/src/sys/alloc/mod.rs', 'std/src/sys/alloc/unix.rs',
         'core/src/ptr/alignment.rs', 'core/src/ptr/non_null.rs',
         'core/src/ptr/unique.rs']
code = '''import hashlib,json,pathlib,subprocess
root=pathlib.Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu')
library=root/'lib/rustlib/src/rust/library'
version=subprocess.check_output([str(root/'bin/rustc'),'-vV'],text=True)
rows=[]
for rel in FILES:
 p=library/rel
 raw=p.read_bytes()
 rows.append(dict(path=rel,host_path=str(p),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),text=raw.decode()))
print(json.dumps(dict(toolchain=version,files=rows)))
'''.replace('FILES', repr(FILES))
if '--check' in sys.argv:
    record = json.loads((E/'std-inputs-D588.json').read_text())
    for row in record['files']:
        raw = (DEST/row['path']).read_bytes()
        assert len(raw) == row['bytes']
        assert hashlib.sha256(raw).hexdigest() == row['sha256']
    assert record['toolchain'] == json.loads(
        Path('evidence/pv-evh10-20261102/adopted-backend-confirmation.json').read_text()
    )['adopted_build_receipt']['receipt']['toolchain']
else:
    import shlex
    result = subprocess.run(['ssh','dombarker@100.108.41.90',
                             'python3 -c '+shlex.quote(code)],
                            capture_output=True, text=True, check=True)
    record = json.loads(result.stdout)
    for row in record['files']:
        p = DEST/row['path']
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(row.pop('text').encode())
    record.update(evidence_class='read-only installed deployed-version rust-src input collection; not allocator adequacy or compiler preservation',
                  command='rustc -vV and reading seven files; no native program execution or compilation',
                  source_to_machine='V370 retained', native_runs=0, kani_runs=0)
    (E/'std-inputs-D588.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS seven std source input hashes and deployed rustc version (check mode verifies toolchain parity)')
