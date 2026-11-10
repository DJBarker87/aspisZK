#!/usr/bin/env python3
"""Aeneas-only run from a saved LLBC (host side, inside an admitted capped scope). Verifies tool and LLBC hashes, runs the spec's aeneas_command, writes PCWN_<run>_PINS.json."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,subprocess,time
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
spec=json.loads((E/(sys.argv[1]+'_spec.json')).read_text());run=spec['run']
tool=Path(spec['aeneas_command'][0]);assert sha(tool.read_bytes())==spec['aeneas_sha256'],'aeneas sha mismatch'
llbc=Path(spec['llbc']);assert llbc.is_file()
out=E/(run+'_emitted');out.mkdir(exist_ok=True)
pins=dict(run=run,aeneas=str(tool),aeneas_sha256=sha(tool.read_bytes()),llbc=str(llbc),llbc_sha256=sha(llbc.read_bytes()),llbc_produced_by=spec['llbc_produced_by'],command=spec['aeneas_command'],frozen_revision=spec.get('frozen_revision'))
t=time.time()
r=subprocess.run(['/usr/bin/time','-v']+spec['aeneas_command'],capture_output=True,text=True,cwd=str(E))
pins.update(exit=r.returncode,wall=time.time()-t)
import re
errs=[l for l in re.sub(r'\x1b\[[0-9;]*m','',r.stdout).splitlines() if re.match(r'\[ *Error',l) or l.startswith('Source:') or 'Could not' in l or 'not supported' in l]
(out/'aeneas.errors').write_text('\n'.join(errs)[:60000]);(out/'aeneas.stdout').write_text(r.stdout[-20000:]);(out/'aeneas.time').write_text(r.stderr[-6000:])
(out/(run+'_PINS.json')).write_text(json.dumps(pins,indent=1))
print(json.dumps(dict(attempt=run,exit=r.returncode)))
sys.exit(r.returncode)
