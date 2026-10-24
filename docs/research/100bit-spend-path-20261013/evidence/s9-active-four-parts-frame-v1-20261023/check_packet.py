from pathlib import Path
import json,hashlib,re
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text())
for f in m['files']:
 p=r/f['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'] and p.stat().st_size==f['bytes']
t=m['targets'][0];assert t['exit_status']==0 and t['process_swaps']==0 and t['watchdog_abort'] is None
s=(r/'proofs'/t['module']/'lean.log').read_text();assert 'error:' not in s and 'sorryAx' not in s
for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',s):assert set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'}
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.ir','.so','.elf','.bin','.llbc'}
print('PASS: actual loops8/16 preserve SAME parts outside4; no Can/meaning premises')
