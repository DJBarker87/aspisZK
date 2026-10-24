from pathlib import Path
import json,hashlib,re
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text());h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for f in m['files']:
 p=r/f['path'];assert h(p)==f['sha256'] and p.stat().st_size==f['bytes']
for t in m['targets']:
 assert t['exit_status']==0 and t['process_swaps']==0 and t['watchdog_abort'] is None
 log=(r/'proofs'/t['module']/'lean.log').read_text();assert 'error:' not in log and 'sorryAx' not in log
 assert 'depends on axioms:' in log
 for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',log):assert set(x.strip() for x in a.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
for d in json.loads((r/'dependencies.json').read_text())['exact_packets']:assert h(r.parent.parent/d['path'])==d['sha256']
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.ir','.so','.elf','.llbc','.bin'}
print('PASS: same supplied point parts/model/common input fold values; security target open')
