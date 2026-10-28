"""Read-only final coherence checks, after the single frozen manifest replay."""
from pathlib import Path
import runpy,hashlib,json
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028')
for script in ['resume-final-fingerprint.py','source-freeze.py','resume-id-audit.py']:
 runpy.run_path(str(D/script),run_name='__main__')
j=json.load(open(D/'resume-id-audit.json'));assert not j['other_job_id_paths'] and not j['shared_sent'];assert sorted(j['own_launched'])==list(range(41400,41500))
T=Path('/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools');pins={'aeneas':'562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19','charon':'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8','charon-driver':'efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45'}
for n,h in pins.items():assert hashlib.sha256((T/n).read_bytes()).hexdigest()==h,n
(D/'resume-final-tool-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
print('Final accepted source/object closure, frozen source, exact100 IDs and extractor pins verified')
