"""Check copied host source bytes against this worktree's tracked git inputs."""
from pathlib import Path
import hashlib,json,subprocess
root=Path(__file__).resolve().parents[2]
base='/home/dombarker/project-offloads/codex-pv-cb3-20261026/source'
code='''import pathlib,hashlib,json
p=pathlib.Path(%r)
print(json.dumps({str(x.relative_to(p)):hashlib.sha256(x.read_bytes()).hexdigest() for x in p.rglob('*') if x.is_file() and not x.is_symlink()}))
'''%base
import shlex
remote=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-c',shlex.quote(code)],text=True))
tracked=set(subprocess.check_output(['git','ls-files'],cwd=root,text=True).splitlines())
rows=[]
for name,sha in remote.items():
 if name in tracked:
  data=(root/name).read_bytes();expected=hashlib.sha256(data).hexdigest()
  rows.append(dict(path=name,sha256=sha,expected_sha256=expected,match=sha==expected))
r=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),snapshot=base,files=rows,mismatches=[x for x in rows if not x['match']],untracked_snapshot_paths=sorted(set(remote)-tracked))
p=root/'evidence/pv-cb3-20261026/source-identity.json';p.write_text(json.dumps(r,indent=2)+'\n')
print('Compared',len(rows),'files;',len(r['mismatches']),'mismatches;',len(r['untracked_snapshot_paths']),'nontracked snapshot paths')
for row in r['mismatches']:print(row['path'])
