#!/usr/bin/env python3
"""Supplement receipts with exact source snapshot/commit byte links."""
import pathlib,json,hashlib,subprocess
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip();rows=[]
for r in map(json.loads,(e/'resume8-attempts.jsonl').read_text().splitlines()):
 path='docs/research/v8-r0-zk-20261009/lean/'+r['module']+'.lean'
 snapshot=e/'sources'/f"{r['attempt']}.lean.txt"
 def commit_sha(c):
  p=subprocess.run(['git','show',c+':'+path],cwd=root,capture_output=True)
  return hashlib.sha256(p.stdout).hexdigest() if p.returncode==0 else None
 current=commit_sha(rev);original=commit_sha(r['source_revision'])
 rows.append(dict(attempt=r['attempt'],accepted=r['accepted'],source_path=path,source_sha256=r['source_sha256'],snapshot_sha256=hashlib.sha256(snapshot.read_bytes()).hexdigest(),recorded_worktree_HEAD=r['source_revision'],recorded_HEAD_contains_exact_source=original==r['source_sha256'],bound_commit=rev if current==r['source_sha256'] else None,binding_recorded_after_run=True))
(e/'resume8-revision-links.json').write_text(json.dumps(dict(note='Original run receipts remain unchanged. A source_revision field there records the worktree HEAD; exact bytes are the hashed snapshot. This supplement explicitly distinguishes dirty-source runs and later matching commit bindings.',rows=rows),indent=2)+'\n')
assert all(r['snapshot_sha256']==r['source_sha256'] for r in rows)
assert all(r['bound_commit'] for r in rows if r['accepted'])
print(len(rows),'snapshots checked;',sum(r['accepted'] for r in rows),'accepted exact commit links;',sum(not r['recorded_HEAD_contains_exact_source'] for r in rows),'dirty-source runs explicitly identified')
