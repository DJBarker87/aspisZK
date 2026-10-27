#!/usr/bin/env python3
"""Bind retained Kani source receipts to their exact recorded revisions."""
import pathlib,json,hashlib,subprocess
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
rows=[]
for inv in map(json.loads,(e/'resume8-kani-invocations.jsonl').read_text().splitlines()):
 p=e/inv['name']/'receipt.json'
 if not p.exists():continue
 r=json.loads(p.read_text());checks=[]
 for path,sha in sorted(r['source_sha256'].items()):
  b=subprocess.check_output(['git','show',r['source_revision']+':'+path],cwd=root)
  checks.append(dict(path=path,recorded_sha256=sha,revision_sha256=hashlib.sha256(b).hexdigest(),equal=sha==hashlib.sha256(b).hexdigest()))
 rows.append(dict(name=inv['name'],revision=r['source_revision'],exit=r['exit_status'],source_checks=checks,all_equal=all(c['equal'] for c in checks),print_axioms=r['print_axioms'],limits=r['limits'],command=r['target']))
(e/'resume8-kani-source-audit.json').write_text(json.dumps(rows,indent=2)+'\n')
print([(r['name'],len(r['source_checks']),r['all_equal']) for r in rows])
assert all(r['all_equal'] for r in rows)
