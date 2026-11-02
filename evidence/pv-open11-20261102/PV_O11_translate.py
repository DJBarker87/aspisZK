from pathlib import Path
import json,subprocess,hashlib
D=Path(__file__).parent
p=D/'extract/PV_O11_ErrorKind.llbc';r=json.loads(p.read_text());assert not r['has_errors']
a=D.parent/'codex-pv-cx-20261029/resume-ae1/pinned-tools/aeneas-ae1-2-fda587d2'
assert hashlib.sha256(a.read_bytes()).hexdigest()=='fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68'
(D/'generated').mkdir(exist_ok=True)
cmd=[str(a),'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace','PV_O11_ErrorKind','-dest',str(D/'generated'),'-split-files','-emit-json',str(p)]
(D/'PV_O11_translate-input.json').write_text(json.dumps(dict(command=cmd,llbc_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),translator_sha256=hashlib.sha256(a.read_bytes()).hexdigest(),identity='functionally identical rebuild (ae1-2)',scope='direct getter extraction, unmodified emitted output; x-prime std parity not yet discharged'),indent=2)+'\n')
r=subprocess.run(cmd);raise SystemExit(r.returncode)
