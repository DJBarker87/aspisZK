#!/usr/bin/env python3
import hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def req(ok,msg):
 if not ok: raise SystemExit('FAIL: '+msg)
m=json.loads((HERE/'manifest.json').read_text())
src=HERE/'sources/S4Tx1InstalledPrepareBridgeV1.lean'
r=json.loads((HERE/'proof/receipt.json').read_text())
req(sha(src)==m['source_sha256']==r['source_sha256'],'target source SHA')
req(r['exit_status']==0 and r['object_sha256']==m['object_sha256'],'successful object receipt')
req(r['process_swaps']==0 and r['wall_seconds']>0 and r['peak_process_rss_bytes']>0,'resource receipt')
profile=(HERE/'proof/LEAN_PATH.txt').read_text().rstrip('\n')
req(hashlib.sha256(profile.encode()).hexdigest()==m['lean_path_sha256'],'exact LEAN_PATH contents')
closure=json.loads((HERE/'proof/closure.json').read_text())
req(closure['missing']==[] and closure['modules']==7608,'resolved imported closure')
for n,o in m['direct_import_owners'].items():
 p=Path(o['path']);req(p.is_file() and sha(p)==o['sha256'],f'direct object {n}')
 req(closure['owners'].get(n,{}).get('sha256')==o['sha256'],f'closure owner {n}')
for n,o in m['source_pins'].items():
 p=HERE/'source-pins'/n;req(p.is_file() and sha(p)==o['sha256'],f'source pin {n}')
cmd=json.loads((HERE/'proof/command.json').read_text())
req(cmd['argv'][-1]==str(Path('/tmp/s4-tx1-installed-prepare-bridge-v1/sources/S4Tx1InstalledPrepareBridgeV1.lean')),'compile target argv')
log=(HERE/'proof/lean.log').read_text()
hits=re.findall(r"'AspisR1S4Tx1InstalledPrepareBridgeV1\.source_caller_reaches_prepared_loop_installed' depends on axioms: \[(.*?)\]",log,re.S)
req(len(hits)==1,'named theorem axioms report')
ax=set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',hits[0]))
req(ax==set(m['axioms']),f'axiom set: {sorted(ax)}')
text=src.read_text();req(not re.search(r'(?m)^\s*(?:sorry|axiom)\b',text),'no proof escapes')
for p in HERE.rglob('*'):
 if p.is_file(): req(p.suffix not in {'.olean','.llbc','.bin'},f'no compiled/binary files: {p}')
print('PASS: focused source, import closure, selected direct owners, receipts, axioms, source-only policy')
