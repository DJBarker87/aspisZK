#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re
ROOT=Path(__file__).resolve().parent
M=json.loads((ROOT/'manifest.json').read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
rec=json.loads((ROOT/M['launch_receipt']).read_text())
pre=json.loads((ROOT/M['preflight']).read_text())
cmd=json.loads((ROOT/M['launch_command']).read_text())
closure=json.loads((ROOT/M['closure']).read_text())
src=ROOT/M['source']; profile=ROOT/M['profile']; log=(ROOT/M['lean_raw_log']).read_text()
assert sha(src)==M['source_sha256']==rec['source_sha256']==pre['source_sha256']
assert rec['object_sha256']==M['external_object_sha256'] and rec['exit_status']==0
assert rec['source_revision_at_launch']==M['source_revision_at_launch']==pre['source_revision']
assert rec['process_swaps']==0 and rec['watchdog_abort'] is None
assert sha(profile)==pre['profile_sha256']
assert cmd['argv'][-1].endswith(src.name)
assert cmd['owner']['target']==M['module']
assert not closure['missing'] and closure['modules']==len(closure['owners'])
for group in (pre['direct_imports'], closure['owners']):
 for mod,pin in group.items():
  p=Path(pin['path'])
  assert p.is_file() and sha(p)==pin['sha256'],f'owner changed: {mod}'
for decl,axs in M['theorems'].items():
 mt=re.search(re.escape("'"+decl+"' depends on axioms:")+r'([^\n]*(?:\n\s+[^\n]*){0,4})',log)
 assert mt, f'missing axioms: {decl}'
 got=mt.group(1)
 assert all(a in got for a in axs) and 'sorryAx' not in got,(decl,got)
assert not list(ROOT.rglob('*.olean'))
for p in ROOT.rglob('*'):
 if p.is_file(): assert p.suffix.lower() not in {'.elf','.so','.dylib','.a'},p
print('PASS: exact source/object/receipt pins, direct imports, recursive closure, axioms, source-only packaging')
