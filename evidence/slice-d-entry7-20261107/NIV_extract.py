from NIV_formal import *
files={n:(E/n).read_text() for n in ['NIV_stage.py','NIV_extract_host.py','NIV_OPACITY.json','NIV_EXTRACTION_PREFLIGHT.json']}
r=run('NIV_L022','extract','entry',['python3','NIV_extract_host.py'],files,{'CARGO_TARGET_DIR':B+'/NIV_NHR_target','CARGO_NET_OFFLINE':'true','RUSTFLAGS':''})
# Recover the attempt read-only regardless of extraction success; never resubmit.
r2=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});paths=[b/'NIV_EXTRACT_LAUNCHED.json']+list((b/'NIV_extracted/entry').rglob('*'))
print(json.dumps({{str(p.relative_to(b)):base64.b64encode(p.read_bytes()).decode() for p in paths if p.is_file()}}))
''');assert r2.returncode==0
import base64
for n,t in json.loads(r2.stdout).items():
 raw=base64.b64decode(t);p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if len(raw)>20*1024*1024:p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw));p.with_name(p.name+'.sha256').write_text(sha(raw)+'\n')
 else:p.write_bytes(raw)
print('EXTRACTION_TERMINAL exit='+str(r['exit_status']),flush=True)
