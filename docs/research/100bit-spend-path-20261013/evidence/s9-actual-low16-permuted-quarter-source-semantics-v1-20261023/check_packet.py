from pathlib import Path
import json,hashlib,re
r=Path(__file__).resolve().parent;base=r.parent.parent;m=json.loads((r/'manifest.json').read_text());h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for f in m['files']:
 p=r/f['path'];assert h(p)==f['sha256'] and p.stat().st_size==f['bytes']
for t in m['targets']:
 assert t['exit_status']==0 and t['process_swaps']==0 and t['watchdog_abort'] is None
 log=(r/'proofs'/t['module']/'lean.log').read_text();assert 'error:' not in log and 'sorryAx' not in log
 for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',log):assert set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'}
for p in json.loads((r/'source-dependencies.json').read_text())['packets']:assert h(base/p['path'])==p['sha256']
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.so','.elf','.bin','.olean','.ilean','.ir','.llbc','.dylib','.dll'}
print('PASS: same actual low16 indexed loops, exact PERM/QUARTER squared and full canonical overwrite; generic powersCan explicit')
