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
rr=json.loads((r/'structural-reuse.json').read_text());s=(base/rr['source']).read_text();span=s[s.index(rr['span_start']):s.index(rr['span_end'])];assert hashlib.sha256(span.encode()).hexdigest()==rr['span_sha256'] and span in (r/'sources/S9CurrentReaderConstructorInputsV1.lean').read_text()
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.ir','.llbc','.so','.dylib','.dll'}
print('PASS: actual-current decoder reader instantiated in same-resume canonical constructor input path; bounded source scope')
