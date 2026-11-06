from NKF_formal import *
# Owned missing output directory, not shared launcher infrastructure.
# K081 remains charged and is NEVER rerun. Link repair is a new support scope.
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{str(p.relative_to(b)):p.read_text() for p in (b/'NKF_native').glob('*.c')}}))
''');assert r.returncode==0
files=json.loads(r.stdout);files['NKF_tmp/.keep']='Owned temporary directory retained for toolchain outputs.\n'
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
rc=run('NKF_L033','link','NKF_ScanDriver',[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NKF_native/NKF_ScanDriver',*[n for n in files if n.endswith('.c')]],files)
assert rc['exit_status']==0
r=ssh('python3',f'''from pathlib import Path
import hashlib,json
p=Path({B!r})/'NKF_native/NKF_ScanDriver';print(json.dumps(dict(scan_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),scan_bytes=p.stat().st_size)))
''');assert r.returncode==0
pins=json.loads((E/'NKF_AUDIT_BINARIES.json').read_text());pins.update(json.loads(r.stdout));(E/'NKF_AUDIT_BINARIES.json').write_text(json.dumps(pins,indent=1)+'\n')
files={'NKF_EXPECTED_IMPORTS.jsonl':(E/'NKF_EXPECTED_IMPORTS.jsonl').read_text(),'NKF_audit_one.py':(E/'NKF_audit_one.py').read_text()}
rc=run('NKF_L034','audit','scan',['python3','NKF_audit_one.py','NKF_native/NKF_ScanDriver','scan',pins['scan_sha256']],files)
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{n:(b/n).read_text()for n in ['NKF_binary_scan.json','NKF_LOADED_scan.jsonl']if(b/n).exists()}}))
''');assert r.returncode==0
for n,t in json.loads(r.stdout).items():
 p=E/('NKF_'+n)
 if n.endswith('.json'):p.write_text(t)
 else:p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
status=json.loads((E/'NKF_JOINT_STATUS.json').read_text());status.update(scan_link=0,scan=rc['exit_status'],scan_link_attempt='NKF_L033',scan_attempt='NKF_L034',excluded_link_failure='NKF_L026 missing owned TMPDIR')
(E/'NKF_JOINT_STATUS.json').write_text(json.dumps(status,indent=1)+'\n')
