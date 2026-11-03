from pathlib import Path
import json,subprocess,hashlib,sys
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029')
x=json.loads((H/'charon.json').read_text())
for p,h in [('/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/charon','daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'),('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1/pinned-tools/aeneas-ae1-2-fda587d2','fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68')]:
 assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h
c=x['command'];i=c.index('--include',c.index('--include')+1) if False else 0
# Value must be opaque: recursive bounded Vec has no valid inductive carrier.
for j in range(len(c)-1):
 if c[j]=='--include' and c[j+1]=='serde_json::value::Value':c[j]='--opaque'
position=c.index('--dest-file')
for name in ['parse_request','pubkey_text','unhex','hex','plan::pk','wallet_fd_path','render_json','print_json','json_string','json_array','json_bool','json_number','json_object','json_into_array','public_lanes','parent_capacity','wallet_open_channel','wallet_read_record','diagnostics::initialize','wallet::output_channel','wallet::return_record']:
 c[position:position]=['--opaque','crate::'+name];position+=2
p=H/'PV_UC_Entry_uc5.llbc';c[c.index('--dest-file')+1]=str(p)
r=subprocess.run(c,cwd=x['cwd']);assert r.returncode==0
assert json.loads(p.read_text())['has_errors'] is False
B=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1/pinned-tools/aeneas-ae1-2-fda587d2')
O=H/'entry-extraction-uc5';O.mkdir(exist_ok=False)
a=[str(B),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','PV_UC_Entry','-dest',str(O),'-split-files','-emit-json',str(p)]
r=subprocess.run(a)
(O/'receipt.json').write_text(json.dumps(dict(charon_command=c,aeneas_command=a,llbc_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),outputs={q.name:hashlib.sha256(q.read_bytes()).hexdigest() for q in O.glob('*.lean')},exit=r.returncode),indent=2)+'\n');sys.exit(r.returncode)
