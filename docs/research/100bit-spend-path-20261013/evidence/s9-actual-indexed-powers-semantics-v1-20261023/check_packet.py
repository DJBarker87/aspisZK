from pathlib import Path
import json,hashlib,re
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text());base=r.parent.parent
assert m['schema']=='focused-extractor-proof-packet-v1' and not m['compiled_objects_included']
for f in m['files']:
 p=r/f['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'] and p.stat().st_size==f['bytes']
for t in m['targets']:
 assert t['exit_status']==0 and t['process_swaps']==0 and t['watchdog_abort'] is None
 l=(r/'proof'/t['name']/'lean.log').read_text();assert 'sorryAx' not in l and 'error:' not in l
 for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',l):assert set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'}
for x in json.loads((r/'source-dependencies.json').read_text())['exact_sources']:assert hashlib.sha256((base/x['path']).read_bytes()).hexdigest()==x['sha256']
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.ir','.llbc','.so','.dylib','.dll'}
print('PASS: exact indexed powers semantic proof targets; source-only/standard axioms/bounded scope')
