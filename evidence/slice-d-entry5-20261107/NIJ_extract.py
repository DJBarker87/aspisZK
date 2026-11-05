from pathlib import Path
import json,hashlib,shutil,subprocess,sys
B=Path(__file__).resolve().parent
P=Path('/home/dombarker/project-offloads/codex-cx-extract-stage-20261106')
pins={'NHR_STAGING_MANIFEST.json': '74a894c5ff7f4f3f3dda624b57891e6d7323fb2fa77c2b850d1c1ab4e3f18ad4', 'NHR_FROZEN_PAYLOAD.json.xz': '58902e9cc80f328a57a4348d6470075505388ff034bcceb36a27d1f4c38118c8', 'NHR_FROZEN_PAYLOAD.json.sha256': '89f8cf69f243878ff24cd659dc6b0269c013ff855af2902578a5e3a76bf9cb39'}
for n,h in pins.items():
 p=P/n;assert hashlib.sha256(p.read_bytes()).hexdigest()==h
 q=B/n
 if q.exists():assert q.read_bytes()==p.read_bytes()
 else:shutil.copy2(p,q)
x=json.loads((B/sys.argv[1]).read_text())
cmd=[sys.executable,str(B/'NIJ_stage.py'),'--extract','--function',x['module'],'--workspace',str(P/'NHR_workspace'),'--out',str(B/'NIJ_extracted'/x['module']),'--opacity',str(B/'NIJ_OPACITY.json')]
assert hashlib.sha256((P/'NHR_workspace/Cargo.lock').read_bytes()).hexdigest()=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
r=subprocess.run(cmd)
(B/'NIJ_extraction_pins.json').write_text(json.dumps(dict(command=cmd,inputs=pins,stager_sha256=hashlib.sha256((B/'NIJ_stage.py').read_bytes()).hexdigest(),exit=r.returncode)))
sys.exit(r.returncode)
