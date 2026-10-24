from pathlib import Path
import json,hashlib,re
r=Path(__file__).resolve().parent;base=r.parent.parent;m=json.loads((r/'manifest.json').read_text());h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for f in m['files']:
 p=r/f['path'];assert h(p)==f['sha256'] and p.stat().st_size==f['bytes']
t=m['targets'][0];assert t['exit_status']==0 and t['process_swaps']==0 and t['watchdog_abort'] is None
log=(r/'proofs'/t['module']/'lean.log').read_text();assert 'error:' not in log and 'sorryAx' not in log
for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',log):assert set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'}
d=json.loads((r/'dependencies.json').read_text())
for p in d['exact_packets']:assert h(base/p['path'])==p['sha256']
old=base/d['reused_original_source']['path'];assert h(old)==d['reused_original_source']['sha256']
s=old.read_text();a=s.index('  have hb := congrArg iota h',s.index('private theorem mapped_inverse_four'));b=s.index('\n/-- Exact native source quarter',a);body=s[a:b].rstrip()+'\n'
assert body==(r/'REUSED-GENERIC-PROOF.txt').read_text() and body in (r/'sources'/ (t['module']+'.lean')).read_text()
assert hashlib.sha256(body.encode()).hexdigest()==json.loads((r/'TEXTUAL-REUSE.json').read_text())['exact_proof_body_sha256']
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.ir','.so','.elf','.bin','.llbc'}
print('PASS: source quarter=model quarter via reused abstract-field API; no concrete inverse conversion; security target open')
