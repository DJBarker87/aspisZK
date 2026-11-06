from pathlib import Path
import hashlib,json,shutil
B=Path(__file__).resolve().parent;P=Path('/home/dombarker/project-offloads/codex-cx-tx1-finish-20261110')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected='92a4901a21af60031077d13d9509dfb497a457d9ad01f75a7117c273d70b1ff2'
assert sha(B/'NLJ_READONLY_NLI_RowSpec136.lean.txt')==expected
r=json.loads((P/'NLI_L011/receipt.json').read_text());assert r['exit_status']==0 and r['source_hashes']['NLI_generated/NLI_RowSpec136.lean']==expected
assert sha(P/'NLI_generated/NLI_RowSpec136.lean')==expected
rows=[]
for suffix in ['.olean','.olean.private','.olean.server','.ir']:
 p=P/'NLI_objects'/('NLI_RowSpec136'+suffix)
 if not p.exists():continue
 q=B/'NLJ_child_seed'/p.name;q.parent.mkdir(exist_ok=True);assert not q.exists();shutil.copyfile(p,q);assert sha(p)==sha(q)
 rows.append(dict(source=str(p),destination=str(q),sha256=sha(q),bytes=q.stat().st_size))
assert any(x['source'].endswith('.olean') for x in rows)
(B/'NLJ_CHILD_OBJECT_PINS.json').write_text(json.dumps(dict(receipt='NLI_L011',source_sha256=expected,files=rows),indent=2))
print('Pinned read-only sibling RowSpec136 object; original module owner retained')
