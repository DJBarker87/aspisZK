from pathlib import Path
import json,hashlib,subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');p=H/'PV_UC_Entry.llbc'
x=json.loads(p.read_text());assert x.get('has_errors') is False,x.keys()
B=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1/pinned-tools/aeneas-ae1-2-fda587d2')
assert hashlib.sha256(B.read_bytes()).hexdigest()=='fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68'
O=H/sys.argv[1];O.mkdir(exist_ok=False)
c=[str(B),'-sequential','-log','Translate','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','PV_UC_Entry','-dest',str(O),'-split-files','-emit-json',str(p)]
(H/(sys.argv[1]+'-command.json')).write_text(json.dumps(dict(command=c,input_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),identity='ae1-2 functionally identical rebuild'),indent=2)+'\n')
sys.exit(subprocess.run(c).returncode)
