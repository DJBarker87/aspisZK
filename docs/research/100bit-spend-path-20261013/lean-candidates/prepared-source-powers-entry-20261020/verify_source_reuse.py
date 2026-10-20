from pathlib import Path
import hashlib,json,subprocess
D=Path(__file__).resolve().parent;R=D.parents[4]
sha=lambda b:hashlib.sha256(b).hexdigest()
report=json.loads((D/'source-declaration-reuse.json').read_text())
old=R/'docs/research/100bit-spend-path-20261013/evidence/s1-current-prepared-extraction-20261020/input'
pins=json.loads((old/'source-pins.json').read_text())
assert pins['revision']==report['original_source_revision']
assert sha((old/'source-pins.json').read_bytes())==report['retained_extraction_pins_sha256']
for target in report['targets'].values():
 rows=[]
 for cut in pins['cuts']:
  fragment=(old/'fragments'/(cut['name']+'.rs')).read_bytes()
  assert sha(fragment)==cut['sha256']
  raw=subprocess.check_output(['git','-C',str(R),'show',target['revision']+':'+cut['path']])
  count=raw.count(fragment)
  rows.append(dict(name=cut['name'],path=cut['path'],body_sha256=sha(fragment),parent_file_sha256=sha(raw),matching_occurrences=count,exact_unchanged=count==1,start_byte=raw.find(fragment) if count==1 else None))
 assert rows==target['declarations']
 assert target['total']==len(rows)==20 and target['unchanged']==20 and all(r['exact_unchanged'] for r in rows)
print('PASS:20 retained production declarations byte-identical in each pinned target; no extraction replay')
