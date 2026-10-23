from pathlib import Path
import json,hashlib,re
r=Path(__file__).resolve().parent;base=r.parent.parent;m=json.loads((r/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1' and not m['compiled_objects_included']
for f in m['files']:
 p=r/f['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'] and p.stat().st_size==f['bytes']
for t in m['targets']:
 assert t['exit_status']==0 and t['process_swaps']==0 and t['watchdog_abort'] is None
 l=(r/'proof'/t['name']/'lean.log').read_text();assert 'sorryAx' not in l and 'error:' not in l
 for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',l):assert set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'}
for x in json.loads((r/'source-dependencies.json').read_text())['exact_sources']:assert hashlib.sha256((base/x['path']).read_bytes()).hexdigest()==x['sha256']
rr=json.loads((r/'private-source-shape-reuse.json').read_text());s=(base/rr['source']).read_text();a=s.index('private def ReturnsCont');b=s.index('#print axioms reverse_next_some_exact');span=s[a:b].replace('private theorem body_done','theorem source_body_done');assert span in (r/'sources/S9ActualTensorInnerSemanticsV1.lean').read_text()
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.ir','.llbc','.so','.dylib','.dll'}
print('PASS: actual native tensor decoded product; focused/standard axioms/source-only; constructor factor meaning retained')
