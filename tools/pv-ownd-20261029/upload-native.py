from pathlib import Path
import base64,subprocess
R=Path(__file__).resolve().parents[2];D='/home/dombarker/project-offloads/codex-pv-ownd-20261029'
code='''from pathlib import Path
import base64,re,shutil
D=Path(DIR);old=Path('/home/dombarker/project-offloads/codex-pv-ownc-20261029')
p=D/'probe';p.mkdir(exist_ok=True)
s=(old/'probe/Cargo.toml').read_text();(p/'Cargo.toml').write_text(s)
for src,dst in [('probe/Cargo.lock','probe/Cargo.lock'),('deployed-units.json','deployed-units.json'),('deployed-client-Cargo.lock','deployed-client-Cargo.lock')]:shutil.copy2(old/src,D/dst)
'''.replace('DIR',repr(D))
for rel,dst in [('tools/pv-ownd-20261029/initial.rs','probe/probe.rs'),('tools/pv-ownd-20261029/native.py','native.py'),('evidence/pv-ownd-20261029/native-inputs.json','native-inputs.json')]:
 b=(R/rel).read_bytes();assert b==subprocess.check_output(['git','show','HEAD:'+rel]);code+=f"(D/{dst!r}).write_bytes(base64.b64decode({base64.b64encode(b).decode()!r}))\n"
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True);assert r.returncode==0
