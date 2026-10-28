"""Remove only this job's solver scratch after its scoped process is terminal."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
assert not (E/'NBR_ACTIVE.json').exists(),'attempt still active'
code='''from pathlib import Path
import json,subprocess,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-native-prepare3-20261028');t=b/'NBR_tmp'
ps=subprocess.check_output(['ps','-eo','pid,args'],text=True)
live=[l for l in ps.splitlines() if str(b/'NBR_target') in l]
assert not live,live
before=[str(p) for p in t.rglob('*') if p.is_file()]
for p in t.iterdir():
 if p.is_dir():shutil.rmtree(p)
 else:p.unlink()
print(json.dumps(dict(own_tmp=str(t),deleted=before,live=live,other_tmp_untouched=True,persistent_cache_untouched=True),indent=2))
'''
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/(sys.argv[1]+'-cleanup.log')).write_text(r.stdout+r.stderr)
assert r.returncode==0,r.stderr
(E/(sys.argv[1]+'-cleanup.json')).write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
