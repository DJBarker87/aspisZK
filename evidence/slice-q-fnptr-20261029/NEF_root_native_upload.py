from NEF_host import *
admit('NEF_ROOTNATIVE001')
files={p.name:p.read_text() for p in E.glob('NEF_root_*.rs.txt')}
r=py(f'''from pathlib import Path
import json
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():(b/n).write_text(t)
''');assert r.returncode==0,r.stderr
