from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent.parent
files=subprocess.check_output(['git','ls-files','crates','programs','Cargo.toml','Cargo.lock','.cargo','docs/research/v8-r0-zk-20261009/z4'],text=True).splitlines()
files=[f for f in files if Path(f).is_file()]
want={f:hashlib.sha256(Path(f).read_bytes()).hexdigest() for f in files}
code='''import json,hashlib
from pathlib import Path
files=json.loads(input())
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit30-20261022/src')
print(json.dumps({f:hashlib.sha256((H/f).read_bytes()).hexdigest() if (H/f).is_file() else None for f in files}))
'''
import shlex
actual=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(files),text=True))
diffs=[dict(path=f,tracked_sha256=want[f],host_sha256=actual[f]) for f in files if want[f]!=actual[f]]
(E/'source-inventory.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),checked=len(files),differences=diffs,source_hashes=want),indent=2)+'\n')
print(len(files),'checked;',len(diffs),'differences:',[x['path'] for x in diffs])
