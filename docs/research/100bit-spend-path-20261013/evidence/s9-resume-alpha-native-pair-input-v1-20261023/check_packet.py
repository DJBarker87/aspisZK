from pathlib import Path
import json,hashlib,re,subprocess,sys
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text());base=r.parent.parent
assert m['schema']=='focused-extractor-proof-packet-v1' and not m['compiled_objects_included']
for f in m['files']:
 p=r/f['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'] and p.stat().st_size==f['bytes']
for t in m['targets']:assert t['exit_status']==0 and t['process_swaps']==0 and t['watchdog_abort'] is None
for d in json.loads((r/'source-dependencies.json').read_text())['exact_sources']:assert hashlib.sha256((base/d['path']).read_bytes()).hexdigest()==d['sha256']
l=(r/'proof/lean.log').read_text();assert 'sorryAx' not in l and 'error:' not in l
for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',l):assert set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'}
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.ir','.llbc','.so','.dylib','.dll'}
for dep in ['s9-resume-alpha-source-canonical-v1-20261023','s9-array-two-prefix-source-v1-20261023']:subprocess.check_call([sys.executable,str(r.parent/dep/'check_packet.py')])
print('PASS: strict resume/source prefix to native Pair alpha; standard-axiom source-only focused proof')
