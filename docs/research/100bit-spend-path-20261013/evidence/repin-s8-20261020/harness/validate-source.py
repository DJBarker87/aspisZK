from pathlib import Path
import hashlib,json
H=Path('/home/dombarker/project-offloads/codex-cx-repin-s8-20261020')
pins=json.loads((H/'harness/source-hashes.json').read_text())
rows=[]
for p,h in pins['files'].items():
 actual=hashlib.sha256((H/'src'/p).read_bytes()).hexdigest()
 rows.append(dict(path=p,expected=h,actual=actual,match=h==actual))
report=dict(source_revision=pins['source_revision'],files=rows,all_match=all(r['match'] for r in rows))
(H/'source-validation.json').write_text(json.dumps(report,indent=2)+'\n')
assert report['all_match']
print(len(rows),'frozen source pins match')
