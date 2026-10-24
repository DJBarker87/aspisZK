from pathlib import Path
import json,hashlib,re
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text())
for f in m['files']:
 p=r/f['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'] and p.stat().st_size==f['bytes']
for t in m['targets']:
 assert t['exit_status']==0 and t['process_swaps']==0 and t['watchdog_abort'] is None
 log=(r/'proofs'/t['module']/'lean.log').read_text();assert 'error:' not in log and 'sorryAx' not in log
 for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',log):assert set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'}
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.ir','.so','.elf','.bin','.llbc'}
print('PASS: six concrete/generic Field operator identities; AST evidence diagnostic only; security target open')
