from pathlib import Path
import subprocess,json,re,hashlib
E=Path(__file__).resolve().parent
jobs=[(28,'NGQ_SamplerNative'),(29,'NGQ_ByteFrames'),(30,'NGQ_ArrayStage'),(31,'NGQ_Normalize'),(32,'NGQ_MaterializeChain'),(33,'NGQ_SamplerPacket'),(34,'NGQ_EventBounds'),(35,'NGQ_Concrete'),(36,'NGQ_DigestRef'),(37,'NGQ_DigestBridge')]
failed=set();skipped=[]
for num,target in jobs:
 a=f'NGQ_L{num:03}';dependencies=re.findall(r'^import (NGQ_\S+)',(E/(target+'.lean')).read_text(),re.M)
 if any(n in failed for n in dependencies):
  skipped.append(dict(attempt=a,module=target,failed_dependencies=[n for n in dependencies if n in failed]));failed.add(target);continue
 r=subprocess.run(['python3',str(E/'NGQ_run.py'),a,'lean',target],text=True,capture_output=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit(a+' missing receipt; recover before proceeding')
 rc=json.loads(p.read_text());print(a,target,rc['exit_status'],rc['wall_seconds'],rc['peak_rss_kib'],flush=True)
 if r.returncode:failed.add(target)
(E/'NGQ_MODEL_SKIPPED.json').write_text(json.dumps(skipped,indent=1)+'\n')
